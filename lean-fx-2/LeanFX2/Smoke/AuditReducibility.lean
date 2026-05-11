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

K12.13 ships (Layer-1 documented SN-fallback for Ty.modal):
* `Reducible Ty.modal modalityTag carrierType term =
  SN(term)`.  Layer 1 kernel has NO Term ctor producing
  `Ty.modal _ _`-typed values (modIntro/modElim/subsume are
  raw-side scaffolding that preserves innerType).  Modal type
  former exists but is uninhabited at the typed layer until
  Layer 6 (#1716 + #1689-1691) lands typed modIntroCross /
  modElimCross with 8-modality dispatch.  K12.13.layer6 will
  then ship the per-modality Tait closure (♭ ⊣ ◇ ⊣ □ ⊣ ♯
  chain + ghost/cap/later/clock).

K12.14 ships (full refineElim closure for Ty.refine):
* `Reducible Ty.refine baseType predicate refinedValue =
  SN(refinedValue) ∧ Reducible baseType (Term.refineElim
  refinedValue)`.  Structurally identical to K12.12 Ty.glue:
  plain projection from Ty.refine to baseType (strict sub-Ty).
  No mode constraint, no quantifier.  Decidable-predicate-
  discharge aspect lives at Layer 5 (#1342 D5.6, #1344 D5.8
  SMTCert), orthogonal to RC closure.

K12.15 ships (4 advanced type formers — 2 full closures + 2 deferred):
* `Reducible Ty.record A r = SN(r) ∧ Reducible A (Term.recordProj r)`
  — full closure via projection (singleFieldType strict sub-Ty).
* `Reducible Ty.codata S O c = SN(c) ∧ Reducible O (Term.codataDest c)`
  — full closure via observation projection.
* `Reducible Ty.session protocolStep t = SN(t)` — Layer-1 SN
  fallback; Sessions layer (#1268 K09) ships per-step closures.
* `Reducible Ty.effect carrier tag e = SN(e)` — Layer-1 SN
  fallback; Effects layer (#1345-#1346) ships handler closures.

Two semantic upgrades (record / codata) plus two documented
Layer-deferrals (session / effect, both blocked on
introducer-only state at Layer 1).

K12.16 ships (architectural documentation — no new arm):
Per lean-fx-2 CLAUDE.md "Cumulativity is a Conv rule (Layer 3+),
not a Ty constructor", there is NO `Ty.cumulUp` ctor.
Cumulativity at the kernel lives EXCLUSIVELY at the Term layer
via `Term.cumulUp`, which produces `Term ctx (Ty.universe
higherLevel _) (RawTerm.cumulUpMarker _)` from a Term at
`Ty.universe lowerLevel _`.  Since Reducible dispatches on Ty
(not Term shape), the universe arm K12.4 already covers
cumulated terms uniformly:
`Reducible (Ty.universe _ _) (Term.cumulUp ...) =
Term.isStronglyNormalizing (Term.cumulUp ...)`.
Universe-cumulativity-awareness is INTRINSIC to K12.4.

What the fundamental lemma's cumulUp case (K12.26) actually
needs is a "SN-preserved-under-cumulUp" lemma at the Reduction
layer, NOT a separate RC closure-tightening.  K12.16 ships
documentation locking in this design.

K12.17 ships RC decidability infrastructure; K12.18-K12.26
ship the fundamental lemma; K12.27 closes M04 /
`strong_normalization`. -/

#print axioms RawStep.parProgress
#print axioms RawTerm.isStronglyNormalizing
#print axioms Term.isStronglyNormalizing
#print axioms Reducible

end LeanFX2.Smoke
