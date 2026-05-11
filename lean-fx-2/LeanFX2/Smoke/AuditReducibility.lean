import LeanFX2.Reducibility

namespace LeanFX2.Smoke

open LeanFX2

/-! K12.1-K12.5 — Tait reducibility-candidate predicate
`Reducible` defined by structural recursion on Ty (25 arms).
Each `#print axioms` line below must report "does not depend
on any axioms".

K12.1 ships:
* `RawStep.parProgress` — non-reflexive parallel reduction
  (a `RawStep.par` step that fires at least one redex).
* `RawTerm.isStronglyNormalizing` — inductive Prop closure
  under non-trivial parallel reduction.  Same shape as Lean's
  `Acc` but emits its own recursor, no Acc dependency.
* `Term.isStronglyNormalizing` — typed SN as raw SN of the
  term's raw projection.

K12.2-K12.4 ship (now expressed as def-equations on Ty):
* Closed-leaf arms `Reducible Ty.{unit,bool,nat,empty,interval,
  universe,tyVar} term = Term.isStronglyNormalizing term`.
  SN matches Tait's base-type clause exactly.

K12.5 ships (architectural pivot):
* `Reducible Ty.arrow A B term = SN(term) ∧ ∀ arg,
  Reducible A arg → Reducible B (Term.app term arg)`.
  Wood/Atkey 2022 corrected Lam rule's reducibility shape.
* Architectural pivot from `inductive Reducible` to
  `def Reducible` by recursion on Ty.  Resolves the
  strict-positivity wall (`Reducible` referenced LEFT of an
  arrow inside a constructor's argument is non-positive).

K12.6 ships (weak dep-Π closure):
* `Reducible Ty.piTy A B term = SN(term) ∧ ∀ arg,
  Reducible A arg → SN(Term.appPi term arg)`.  Weak variant —
  the full Tait dep-Π clause recurses on the substituted
  codomain `B.subst0 A arg`, which fails structural recursion
  (substituted codomain is not a strict sub-term).  Weak
  closure recurses only on `domainType` (strict sub-term)
  and demands SN of the application result.

K12.7 ships (asymmetric Σ closure):
* `Reducible Ty.sigmaTy A B term = SN(term) ∧
  Reducible A (Term.fst term) ∧ SN(Term.snd term)`.
  Asymmetric: full Reducible on fst projection (firstType IS
  a strict sub-term of `Ty.sigmaTy firstType secondType`,
  structural recursion works), weak SN on snd projection (its
  type is `secondType.subst0 firstType (RawTerm.fst pairRaw)`
  — substituted, same wall as K12.6 piTy codomain).  Full
  Reducible-snd closure reserved for the Kripke refactor.

K12.8 ships (weak elim closure for parametric inductives):
* `Reducible Ty.listType A xs = SN(xs) ∧ ∀ motiveType
  nilBranch consBranch, SN(nilBranch) ∧ (∀ head tail,
  Reducible A head → SN(tail) → SN(app(app consBranch head)
  tail)) → SN(listElim xs nilBranch consBranch)`.
* `Reducible Ty.optionType A xs = SN(xs) ∧ ∀ motiveType
  noneBranch someBranch, SN(noneBranch) ∧ (∀ v, Reducible A v
  → SN(app someBranch v)) → SN(optionMatch xs noneBranch
  someBranch)`.
* `Reducible Ty.eitherType L R xs = SN(xs) ∧ ∀ motiveType
  leftBranch rightBranch, (∀ v, Reducible L v → SN(app
  leftBranch v)) ∧ (∀ v, Reducible R v → SN(app rightBranch
  v)) → SN(eitherMatch xs leftBranch rightBranch)`.
  Each parametric type's element / left / right sub-Ty IS
  a strict sub-Ty, so full Reducible recurses on branches'
  argument types; motiveType is arbitrary (NOT structural
  sub-Ty) so conclusion demotes to SN of the eliminator
  result.  Mirrors K12.6 piTy weak closure pattern.

K12.9 ships (HoTT identity weak idJ closure):
* `Reducible Ty.id carrier left right witness = SN(witness) ∧
  ∀ motiveType baseCase, SN(baseCase) → SN(Term.idJ baseCase
  witness)`.  The id-eliminator's output `motiveType` is
  arbitrary (NOT structural sub-Ty), so conclusion demotes to
  SN of idJ result.  Mirrors K12.6 piTy weak closure pattern.

K12.10 ships (HoTT observational + strict identity weak J closures):
* `Reducible Ty.oeq carrier left right witness = SN(witness) ∧
  ∀ motiveType baseCase, SN(baseCase) → SN(Term.oeqJ baseCase
  witness)`.  Same shape as K12.9 RC.id.
* `Reducible Ty.idStrict carrier left right witness = SN(witness)
  ∧ ∀ (modeIsStrict : mode = Mode.strict) motiveType baseCase,
  SN(baseCase) → SN(Term.idStrictRec modeIsStrict baseCase
  witness)`.  Universal-quantifies the mode-strict witness; when
  the ambient mode ≠ strict, the equation is uninhabited and the
  inner ∀ is vacuous (closure reduces to SN(witness)).

K12.11 ships (full K12.5-arrow-strength equivalence closure):
* `Reducible Ty.equiv A B equivTerm = SN(equivTerm) ∧ ∀ arg,
  Reducible A arg → Reducible B (Term.equivApp equivTerm arg)`.
  Both A and B are strict sub-Ty of `Ty.equiv A B`, so the
  closure recurses Reducible on both sides (NOT a weak SN
  closure — full K12.5 arrow shape).  Term.equivApp mirrors
  Term.app structurally.

K12.12 ships (cubical path + glue full-output closures):
* `Reducible Ty.path A x y pathTerm = SN(pathTerm) ∧ ∀
  (modeIsUnivalent), ∀ intervalTerm, SN(intervalTerm) → Reducible
  A (Term.pathApp pathTerm intervalTerm)`.  carrier is strict
  sub-Ty so output recurses Reducible.  intervalTerm demoted to
  SN (Ty.interval is sibling Ty ctor, NOT structural sub-Ty of
  Ty.path — Lean recursion checker bans the call; K12.4 says SN
  is propositionally equivalent).
* `Reducible Ty.glue B w gluedValue = SN(gluedValue) ∧ ∀
  (modeIsUnivalent), Reducible B (Term.glueElim gluedValue)`.
  baseType strict sub-Ty → full Reducible on projection result.

Future K12.13-K12.16 tighten the remaining ~6 SN-fallback arms
(refine / record / codata / session / effect / modal) to their
type-former-specific closures.  K12.18-K12.26 ship the
fundamental lemma; K12.27 closes M04 / `strong_normalization`. -/

#print axioms RawStep.parProgress
#print axioms RawTerm.isStronglyNormalizing
#print axioms Term.isStronglyNormalizing
#print axioms Reducible

end LeanFX2.Smoke
