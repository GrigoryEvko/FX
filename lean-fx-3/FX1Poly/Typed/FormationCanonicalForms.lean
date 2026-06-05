import FX1Poly.Typed.EmptyTypeValueInversion

/-! # FX1Poly/Typed/FormationCanonicalForms — canonical forms for the formation engine `HasTypeDesc`

The formation engine `HasTypeDesc` (the moonshot core: var / conv / universeFormation / the generic
`genFormation` former arm) has NO introduction or elimination forms — it types only type FORMERS (Π / Σ via
`genFormation`), universe CODES (`universeFormation`), variables (`var`), and conversions thereof (`conv`).  So
every formation-typed cell is, up to the variable leaf, a Π / Σ former head or a universe-code head — there is no
λ, no application, no data constructor in this engine's reach.

This file proves that characterization and its CLOSED corollary, the structural progress fact the consistency /
canonicity arguments consume: a CLOSED formation-typed term has head generator exactly one of `gen_piTyCode`,
`gen_sigmaTyCode`, `gen_universeCode`.  Combined with the value-case `Conv`-rigidity inversions
(`EmptyTypeValueInversion`: no Π / Σ former or universe code is typed at `emptyTypeCell`), this is the
formation-engine half of the SN-050 / SN-047 canonicity spine — and the `ofFormation` foundation of the eventual
grown-engine canonical forms (where the `piElim` application case is additionally killed by β-redex
non-normality).

## Why the general statement carries a variable disjunct

`HasTypeDesc.var` types `variableCell index` (head `gen_var`), which is NOT a former/universe head — so the
characterization is FALSE for a general (open) context.  The general lemma therefore states a four-way
disjunction WITH the variable case; the closed corollary then discharges that disjunct via the emptiness of
`Fin 0`.  Stating it generally is what lets the induction proceed without a scope-`0` side condition threaded
through every arm: the `conv` arm returns the (subject-unchanged) IH, and the leaf/former arms hit their head
disjunct directly.

## Zero-axiom verification

`HasTypeDesc.rec` (the propext-free mutual recursor, with a trivial `True` telescope motive_2), `by_cases` on
the decidable `Generator` equality, the established `unfold typingRuleDescOf` + `if_neg` + `contradiction`
non-former branch, `rcases` on the disjunction, and `Fin.elim0`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Formation-engine canonical forms (general context).**  A `HasTypeDesc`-typed subject is a variable, or its
head generator is `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode`.  Proved by the propext-free mutual
recursor: `var` hits the variable disjunct; `conv` returns the subject-unchanged IH; `universeFormation` is a
universe head; `genFormation` reads its head off the `typingRuleDescOf` table (Π / Σ, the non-former branch
discharged by `if_neg` + `contradiction`). -/
theorem HasTypeDesc.subjectIsVariableOrFormerHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    (∃ index : Fin scope, subject = variableCell index) ∨
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  refine HasTypeDesc.rec
    (motive_1 := fun {_scope} _context subject _classifier _typed =>
      (∃ index : Fin _scope, subject = variableCell index) ∨
      RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
      RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
      RawTerm.headGenerator subject = Generator.gen_universeCode)
    (motive_2 := fun _context _levels _flag _children _telescope => True)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope typed
  · intro _scope _context index
    exact Or.inl ⟨index, rfl⟩
  · intro _scope _context _subject _classifier _reclassifier _levelExpr _flag _typed _converts
      _reclassifierTyped subjectIH _reclassifierIH
    exact subjectIH
  · intro _scope _context levelExpr flag
    exact Or.inr (Or.inr (Or.inr rfl))
  · intro _scope _context generator payload children levels flag rule isFormation premises _premisesIH
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inr (Or.inl (by subst isPi; rfl))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inr (Or.inr (Or.inl (by subst isSigma; rfl)))
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPi, if_neg isSigma] at isFormation
        contradiction
  · intro _baseScope _currentDepth _context _flag
    exact True.intro
  · intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped _headIH _restIH
    exact True.intro

/-- **Closed formation-engine canonical forms.**  At the empty context the variable disjunct of
`HasTypeDesc.subjectIsVariableOrFormerHead` is vacuous (`Fin 0` is empty), so a CLOSED formation-typed subject's
head generator is exactly one of `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode`.  This is the structural
progress fact the closed-consistency / closed-canonicity arguments consume: a closed formation-typed term is a
type former or a universe code, and the value-case `Conv`-rigidity inversions refute each at `emptyTypeCell`. -/
theorem HasTypeDesc.closedSubjectHeadIsFormerOrUniverse {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
    RawTerm.headGenerator subject = Generator.gen_universeCode := by
  rcases HasTypeDesc.subjectIsVariableOrFormerHead typed with ⟨index, _⟩ | rest
  · exact index.elim0
  · exact rest

end FX1Poly.Typed
