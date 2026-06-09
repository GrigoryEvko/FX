import FX1Poly.Typed.HasTypeDescPiRootGeneric
import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.UniverseClassificationUnique

/-! # FX1Poly/Typed/NeutralClassifierUnique — neutral classifier-class uniqueness
     (route-H reflection, enrichment brick E2.6 — table-generic, UNCONDITIONAL)

The flag-negotiation spine lift: any two grown classifiers of one NEUTRAL subject are `Conv`,
with NO well-formedness premise anywhere.

  * `HasTypeDescPi.untypedAtNonGrownRoot` — the GENERIC refutation: a subject whose root carries
    no formation rule and is none of `gen_var`/`gen_universeCode`/`gen_lam`/`gen_app` has no
    grown typing.  One corollary of the table-generic `subjectRootGeneratorGeneric` covers ALL
    10 eliminator neutrals uniformly and survives formation-table growth (a new former row
    changes nothing here).  Note the per-engine honesty distinction: 6 of the 10 eliminator
    heads have rows in OTHER tables (`hasSomeTypingRule` = true), so the all-engine
    `isUntypableHead` route does NOT cover them — this lemma is the grown-engine-specific
    classification.
  * `HasTypeDescPi.neutralClassifierUnique` — the spine induction: the variable leaf is
    `inversionVariable` (both classifiers Conv the fixed lookup); the application node inverts
    both typings (`invertApp`), applies the IH to the neutral function, splits the two Π
    classifiers with `Conv.piTyCode_inj`, and re-instantiates with `Conv.subst`; every
    eliminator head refutes by `untypedAtNonGrownRoot`.
  * `HasTypeDescPi.neutralUniverseClassificationUnique` — the negotiation lemma the
    flag-coherent extraction (E3) consumes: a neutral's two grown universe classifications
    agree on (level, flag), via `Conv.universeCode_injective`.  Generalizes the shipped var
    leaf (`variableUniverseClassificationUnique`).

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Generic non-grown-root untypability**: a subject whose root generator carries no formation
rule and is none of `gen_var`/`gen_universeCode`/`gen_lam`/`gen_app` has NO grown typing — the
direct corollary of the table-generic `subjectRootGeneratorGeneric`.  Covers every eliminator
head uniformly and survives formation-table growth (a new former row changes nothing here). -/
theorem HasTypeDescPi.untypedAtNonGrownRoot {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (noFormationRule : typingRuleDescOf subject.rootGenerator = none)
    (notVar : subject.rootGenerator ≠ Generator.gen_var)
    (notUniverse : subject.rootGenerator ≠ Generator.gen_universeCode)
    (notLam : subject.rootGenerator ≠ Generator.gen_lam)
    (notApp : subject.rootGenerator ≠ Generator.gen_app) : False := by
  rcases typed.subjectRootGeneratorGeneric with
    isVar | isUniverse | isLam | isApp | ⟨rule, isFormer⟩
  · exact notVar isVar
  · exact notUniverse isUniverse
  · exact notLam isLam
  · exact notApp isApp
  · rw [noFormationRule] at isFormer
    exact nomatch isFormer

/-- **Neutral classifier-class uniqueness, UNCONDITIONAL**: any two grown classifiers of one
NEUTRAL subject are `Conv`.  Spine induction: the variable leaf is `inversionVariable` (both
classifiers Conv the fixed lookup); the application node inverts both typings, applies the IH to
the neutral function (the two Π classifiers are Conv), splits with Π-injectivity, and
re-instantiates with `Conv.subst`; every eliminator head is grown-untypable
(`untypedAtNonGrownRoot`).  No well-formedness premise — every ingredient is wf-free. -/
theorem HasTypeDescPi.neutralClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (neutral : IsNeutral subject) :
    ∀ {firstClassifier secondClassifier : RawTerm scope},
      HasTypeDescPi profile context subject firstClassifier →
      HasTypeDescPi profile context subject secondClassifier →
      Conv firstClassifier secondClassifier := by
  induction neutral with
  | var index =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      exact Conv.trans firstTyped.inversionVariable secondTyped.inversionVariable.sym
  | app headIsNeutral headIH =>
      intro firstClassifier secondClassifier firstTyped secondTyped
      obtain ⟨firstDomain, firstCodomain, firstFunctionTyped, _firstArgumentTyped, firstConv⟩ :=
        HasTypeDescPi.invertApp firstTyped
      obtain ⟨secondDomain, secondCodomain, secondFunctionTyped, _secondArgumentTyped,
        secondConv⟩ := HasTypeDescPi.invertApp secondTyped
      obtain ⟨_domainsConv, codomainsConv⟩ :=
        Conv.piTyCode_inj (headIH firstFunctionTyped secondFunctionTyped)
      exact Conv.trans firstConv
        (Conv.trans (Conv.subst _ codomainsConv) secondConv.sym)
  | fst argumentIsNeutral _argumentIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | snd argumentIsNeutral _argumentIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | boolElim scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | natElim scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | natRec scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | listElim scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | optionMatch scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | eitherMatch scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | idJ scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim
  | idStrictRec scrutineeIsNeutral _scrutineeIH =>
      intro firstClassifier secondClassifier firstTyped _secondTyped
      exact (firstTyped.untypedAtNonGrownRoot rfl
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)
        (fun h => Generator.noConfusion h) (fun h => Generator.noConfusion h)).elim

/-- **Universe classification is unique at every NEUTRAL** — the negotiation lemma the
flag-coherent extraction consumes, generalizing the shipped var leaf: a neutral's two grown
universe classifications agree on (level, flag).  Unconditional. -/
theorem HasTypeDescPi.neutralUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject : RawTerm scope}
    (neutral : IsNeutral subject)
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeDescPi profile context subject
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeDescPi profile context subject
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag :=
  Conv.universeCode_injective
    (HasTypeDescPi.neutralClassifierUnique neutral firstClassified secondClassified)

end FX1Poly.Typed

