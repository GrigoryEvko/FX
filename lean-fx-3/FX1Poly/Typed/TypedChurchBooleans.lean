import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Core.ConvCongruence

/-! # Foundation/PolyCell/Typed/TypedChurchBooleans
    — the Church-boolean encoding, typed by the grown engine

The grown engine `HasTypeDescPi` is Π/FORMATION-ONLY: it types universe/Π/Σ/data-type-code FORMATION and
λ-introduction / application, but the data CONSTRUCTORS (`boolTrue`, `boolFalse`, `pair`, `zero`, `succ`, …)
are PROVEN UNTYPED (`HasTypeDescPiDataHeadUntyped.lean`).  A natural question: does that make the typed
fragment unable to express data?  No — the polymorphic Π-fragment encodes data by the CHURCH ENCODING, and
this file exhibits the booleans concretely.

A Church boolean is a polymorphic selector `Π(A:Type@0). Π(t:A). Π(f:A). A` — given a result type `A` and two
candidates `t f : A`, it returns one of them:

  * `churchTrue  = λ(A:Type@0). λ(t:A). λ(f:A). t` returns the FIRST candidate (`t` = de Bruijn var 1);
  * `churchFalse = λ(A:Type@0). λ(t:A). λ(f:A). f` returns the SECOND candidate (`f` = de Bruijn var 0).

Both are typed by the grown engine end-to-end via THREE nested `piIntro`s — one universe binder and two
type-variable binders — over the nested dependent codomain `Π(t:A). Π(f:A). A` (a two-level Π-FORMATION over
the type variable, `churchOuterArrow`, itself nesting `churchInnerArrow`).  The bodies type by the `var` rule:
`churchTrue`'s body `t` is the non-innermost variable (its weakened lookup resolves to the codomain `A`), so it
exercises a deeper de Bruijn lookup than the polymorphic identity (whose body is always the innermost
variable).  Feeding each derivation through SN-043 (`HasTypeDescPi.closedStronglyNormalizing`) shows both
encodings are strongly normalizing.

The significance: the formation-only typed fragment, despite rejecting the primitive boolean constructors,
DOES type the Church-encoded booleans and proves them terminating — the Π-fragment is computationally
expressive enough to encode the data it cannot primitively introduce.  This file then closes the arc: the
β-SELECTION (`churchTrue` applied to `A t f` β-reduces to `t`, `churchFalse` to `f`) and the resulting
NON-CONVERTIBILITY `churchTrue ≢ churchFalse` — definitional equality genuinely distinguishes the two
encodings, through their computation rather than their syntax.

Zero-axiom: every derivation is a direct constructor application; the only non-trivial steps are the nested
`lmaxAll` level threading (the codomain `Π(t:A).Π(f:A).A` lives at `lmax 0 (lmax 0 0)`) and the `var`-lookup
defeqs at de Bruijn depths 0–2, all of which hold by computation.  No `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, or `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- In context `[A:Type@0, t:A]`, the type `Π(f:A). A` is a Π-formation over the type variable `A` (now at
the deeper indices `domain = var 1`, `codomain = var 2`), typed at `Type@(lmax 0 0)` by `genFormationPi` — the
deep-context twin of `dependentArrowOverTypeVariable_hasTypeDescPi`. -/
theorem churchInnerArrow {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      ((TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag)).cons
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero, LevelExpr.lzero] flag { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
    · exact DescTelescopePi.nil _ _

/-- In context `[A:Type@0]`, the nested dependent function type `Π(t:A). Π(f:A). A` is a Π-formation whose
domain `t:A` is the type variable (`var 0`) and whose codomain `Π(f:A).A` is the inner arrow (a former, not a
variable) — typed at `Type@(lmax 0 (lmax 0 0))` by `genFormationPi` over `churchInnerArrow`. -/
theorem churchOuterArrow {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero, lmaxAll [LevelExpr.lzero, LevelExpr.lzero]] flag
    { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact churchInnerArrow flag
    · exact DescTelescopePi.nil _ _

/-- ★ The Church boolean `true`, `λ(A:Type@0). λ(t:A). λ(f:A). t`, typed at
`Π(A:Type@0). Π(t:A). Π(f:A). A` — the polymorphic selector that returns its FIRST candidate.  Via three
nested `piIntro`s; the body `t` (de Bruijn `var 1`, the non-innermost binder) types by the `var` rule, its
weakened lookup resolving to the codomain `A` (`var 2`). -/
theorem churchTrue_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc
    (lmaxAll [LevelExpr.lzero, lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · exact churchOuterArrow flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero
      (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag ?midDomainTyped ?midCodomainTyped ?midBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    · exact churchInnerArrow flag
    · refine HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero flag
        ?inDomainTyped ?inCodomainTyped ?inBodyTyped
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))

/-- The Church boolean `true` is strongly normalizing — SN-043 on the concrete nested-`piIntro` derivation. -/
theorem churchTrue_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))))
        : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchTrue_hasTypeDescPi (profile := profile) flag)

/-- ★ The Church boolean `false`, `λ(A:Type@0). λ(t:A). λ(f:A). f`, typed at the SAME type
`Π(A:Type@0). Π(t:A). Π(f:A). A` — the polymorphic selector that returns its SECOND candidate.  Same
classifier as `churchTrue`; the body `f` (de Bruijn `var 0`, the innermost binder) types by the `var` rule. -/
theorem churchFalse_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc
    (lmaxAll [LevelExpr.lzero, lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · exact churchOuterArrow flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero
      (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag ?midDomainTyped ?midCodomainTyped ?midBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    · exact churchInnerArrow flag
    · refine HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero flag
        ?inDomainTyped ?inCodomainTyped ?inBodyTyped
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
      · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 2⟩ : Fin 3))

/-- The Church boolean `false` is strongly normalizing — SN-043 on its concrete derivation. -/
theorem churchFalse_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchFalse_hasTypeDescPi (profile := profile) flag)

/-! ## β-selection — the Church booleans COMPUTE the correct branch

Beyond typing and normalization, the Church booleans must COMPUTE: applied to a type and two branches, the
encoding selects the right one.  This is the genuine point of the encoding — the polymorphic Π-fragment
expresses booleans AND its β-reduction realizes the eliminator.

Applied to `Type@0` (the type argument), `Type@0` (the `then` branch) and `Type@1` (the `else` branch), the
two encodings reduce — in three β-steps each (two under the application's function-position congruence, then
the outer β) — to DIFFERENT results: `churchTrue` to the `then` branch `Type@0`, `churchFalse` to the `else`
branch `Type@1`.  So on identical inputs the two encodings compute distinct selections — the booleans are
computationally distinguished, not merely distinct syntax.

A de Bruijn subtlety governs how far this generalizes: `churchFalse`'s body is the INNERMOST variable
(`var 0`), which the final `subst0` replaces DIRECTLY, so the selection holds for ARBITRARY (even symbolic)
branches by computation.  `churchTrue`'s body is the NON-innermost `var 1`, whose resolution threads the
`subst0` lifting fold — which only fully reduces on CONCRETE closed arguments (it stays stuck on a symbolic
branch); hence the concrete branches here.  The non-convertibility corollary `churchTrue ≢ churchFalse` that
follows from these distinct selections is discharged below; the universal `churchTrue` selection (for ARBITRARY
branches, provable via a substitution lemma rather than computation) remains a natural follow-up.
-/

/-- ★ `churchTrue` applied to `Type@0` and the two branches `Type@0` / `Type@1` β-reduces (three steps) to
the FIRST branch `Type@0` — the encoding selects the `then` branch.  Concrete branches: the non-innermost
body `var 1` only resolves through the `subst0` fold on concrete closed arguments. -/
theorem churchTrue_selectsThenBranch (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell
          (lamCell (lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)))))
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (universeCodeCell LevelExpr.lzero flag) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons (universeCodeCell LevelExpr.lzero flag) .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-- ★ `churchFalse` applied to the SAME arguments β-reduces (three steps) to the SECOND branch `Type@1` — the
encoding selects the `else` branch.  Together with `churchTrue_selectsThenBranch`, on identical inputs the two
encodings compute DIFFERENT results (`Type@0` vs `Type@1`): the booleans are computationally distinguished. -/
theorem churchFalse_selectsElseBranch (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell
          (lamCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons (universeCodeCell LevelExpr.lzero flag) .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-! ## Non-convertibility — the two encodings are definitionally distinct

The β-selections show `churchTrue` and `churchFalse` COMPUTE different results on identical inputs.  That
computational difference forces the two encodings to be NON-CONVERTIBLE, and the proof routes through the
observable behaviour rather than through the syntax of the two lambda bodies (which differ only in a de Bruijn
index — a payload distinction that would need a `propext`-risky variable-index inspection to expose directly):

  * applied to identical arguments `Type@0 / Type@0 / Type@1`, were `churchTrue ≡ churchFalse`, congruence of
    conversion (`Conv.app_cong`, three layers) would make the two applications convertible;
  * the selections then reduce those applications to `Type@0` and `Type@1` respectively, so transitivity would
    force `Type@0 ≡ Type@1`;
  * but distinct universe levels are NOT definitionally equal — their codes are distinct no-step normal forms,
    so `Conv` collapses to syntactic `Eq` (`Conv.iff_eq_of_noStep`), which the `propext`-free
    `DecidableEq (RawTerm 0)` refutes.

So the kernel genuinely distinguishes the two Church booleans — through their computational behaviour, the
value-level discrimination canonicity rests on (compare `ConvValueDiscrimination` for the primitive values).
Zero-axiom: the only non-`rfl` steps are `Conv.iff_eq_of_noStep`, `noStep_universeCode`, the conversion
equivalence/congruence lemmas, and a `decide` over the structural `DecidableEq` (no `native_decide`).
-/

/-- The bare Church-`true` lambda term `λ(A:Type@0). λ(t:A). λ(f:A). t` (body the non-innermost `var 1`). -/
abbrev churchTrueLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))))

/-- The bare Church-`false` lambda term `λ(A:Type@0). λ(t:A). λ(f:A). f` (body the innermost `var 0`). -/
abbrev churchFalseLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))

/-- The universe code `Type@0` at the `standard` flag — the type argument and the `then` branch of the
selection fixtures. -/
abbrev churchTypeZeroCode : RawTerm 0 := universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The universe code `Type@1` at the `standard` flag — the `else` branch of the selection fixtures. -/
abbrev churchTypeOneCode : RawTerm 0 := universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard

/-- The universe codes `Type@0` and `Type@1` are NOT convertible: distinct universe levels are not
definitionally equal.  Both are no-step normal forms, so `Conv` collapses to syntactic equality
(`Conv.iff_eq_of_noStep`), which the `propext`-free `DecidableEq (RawTerm 0)` refutes — the universe-level
analogue of `boolTrue ≢ boolFalse`. -/
theorem churchTypeZeroCode_notConvertible_churchTypeOneCode : ¬ Conv churchTypeZeroCode churchTypeOneCode :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun _ step => noStep_universeCode _ step)
          (fun _ step => noStep_universeCode _ step)).mp convertibility)
      (by decide)

/-- ★ `churchTrue` and `churchFalse` are NOT convertible — definitional equality distinguishes the two Church
booleans.  Not because their lambda bodies differ syntactically (`var 1` vs `var 0`, a de Bruijn payload
distinction), but because they COMPUTE differently: applied to `Type@0 / Type@0 / Type@1` they select `Type@0`
vs `Type@1`, so a hypothetical `churchTrue ≡ churchFalse` would — by three layers of application congruence
plus the selections — force the non-equal universe codes `Type@0 ≡ Type@1`, contradicting
`churchTypeZeroCode_notConvertible_churchTypeOneCode`.  The computational distinction the booleans exist to express is thus
also a definitional one. -/
theorem churchTrue_notConvertible_churchFalse : ¬ Conv churchTrueLambda churchFalseLambda := by
  intro convFunctions
  have convApplied :
      Conv (appCell (appCell (appCell churchTrueLambda churchTypeZeroCode) churchTypeZeroCode) churchTypeOneCode)
           (appCell (appCell (appCell churchFalseLambda churchTypeZeroCode) churchTypeZeroCode) churchTypeOneCode) :=
    Conv.app_cong
      (Conv.app_cong
        (Conv.app_cong convFunctions (Conv.refl _))
        (Conv.refl _))
      (Conv.refl _)
  have convOutputs : Conv churchTypeZeroCode churchTypeOneCode :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchTrue_selectsThenBranch UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchFalse_selectsElseBranch UniverseFlag.standard)))
  exact churchTypeZeroCode_notConvertible_churchTypeOneCode convOutputs

end FX1Poly.Typed
