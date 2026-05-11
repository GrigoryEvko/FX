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

K12.17 ships (universal extraction lemma):
* `Reducible.isStronglyNormalizing : Reducible ty term →
  Term.isStronglyNormalizing term`.  Per-Ty case-split across
  all 25 arms: extracts the SN component from each Reducible
  body (either the witness itself for SN-direct arms, or
  `witness.1` for conjunctive arms K12.5-K12.15).  Foundational
  extractor for the fundamental-lemma cascade (K12.18-K12.26)
  to conclude SN from any Reducible witness at any Ty.

K12.18/K12.19 ship (substitution-reducibility predicate + var case):
* `ReducibleSubst termSubst` — for every variable position, the
  per-position typed term supplied by `TermSubst` is `Reducible` at
  the substituted source-type.  K12.18's first cut ∃-packaged the
  witness; K12.19's audit revealed the existential cannot supply
  reducibility of the SPECIFIC term `Term.subst termSubst _` requires,
  so the predicate is reshaped to take `TermSubst` directly.  Same
  predicate name; same zero-axiom discipline; corrected shape.
* `Reducible.fundamental_var` — the var case of the fundamental
  lemma.  `Term.subst termSubst (Term.var position)` reduces
  definitionally to `termSubst position` (via `Term.subst`'s var
  equation), so the proof body is literally `substReducible
  position`.  Foundational base case the K12.20-K12.26 cascade
  builds on.

K12.19.B ships (introducer-SN nullary base cases):
* `RawTerm.unit_isStronglyNormalizing` / `boolTrue_` / `boolFalse_`
  / `natZero_isStronglyNormalizing` — each nullary introducer is
  SN.  Proof: any `parProgress` step requires `source ≠ target`,
  but per `Reduction/RawParInversion.lean`'s `*_inv` lemmas, every
  `RawStep.par` from a nullary canonical introducer is `refl`
  (target = source).  Contradiction discharges the closure.
* `Reducible.fundamental_unit` / `fundamental_boolTrue` /
  `fundamental_boolFalse` / `fundamental_natZero` — the four
  fundamental-lemma cases for nullary intro Term ctors.  Each body
  is literally the corresponding raw SN lemma because Term.subst's
  equation makes `Term.subst termSubst Term.X = Term.X`,
  Reducible's closed-leaf arm unfolds to SN, and Term.SN unfolds
  to RawTerm.SN at the carrier raw.

K12.20.A ships (lam SN preservation):
* `RawTerm.lam_isStronglyNormalizing` — if body is SN then
  `RawTerm.lam body` is SN.  Standard inductive argument on body's
  SN witness via the `lam_inv` step inversion + `RawTerm.lam`
  ctor-injectivity.  Foundational prerequisite for K12.20's
  Term.lam fundamental-lemma case (which still needs CR3 +
  ReducibleSubst.singleton infrastructure to fully discharge).

K12.20.B ships (raw CR2 — SN closure under reduction):
* `RawTerm.isStronglyNormalizing.step_preserves` — given SN of
  source and a parProgress step source → target, SN of target
  follows by destructuring SN's inductive constructor.  CR2 at
  typed Reducible for SN-direct arms (unit/bool/nat/empty/interval/
  universe/tyVar/session/effect/modal) reduces to this raw fact
  via Reducible's definitional unfolding chain.  Compound-arm
  CR2 (arrow/Σ/id/list/...) needs per-Ty case analysis on the
  closure structure — those land in follow-ups.

K12.20.C ships (neutral + natSucc SN preservation):
* `RawTerm.var_isStronglyNormalizing` — every variable is SN
  (vacuous closure: `var_inv` forces `target = var`, contradicting
  `parProgress`'s distinctness clause).  Foundational neutral base
  for CR3 / fundamental-lemma cases that reduce a Term to a `var`
  in a substituted context.
* `RawTerm.natSucc_isStronglyNormalizing` — `natSucc predecessor`
  is SN whenever its predecessor is.  Same shape as K12.20.A
  `lam_isStronglyNormalizing`: induct on predecessor's SN
  witness, invert the step via `natSucc_inv`, use ctor injectivity
  to discharge the distinctness obligation.  Mirrors the only
  unary value-introducer pattern at the raw level; the typed
  `Term.natSucc` fundamental-lemma case (K12.20.G) will compose
  this raw lemma with `Reducible.isStronglyNormalizing` to lift
  reducibility through the constructor.

K12.20.D ships (typed CR2 lift for 10 SN-direct Reducible arms):
* `Reducible.step_preserves_{unit,bool,nat,empty,interval,
  universe,tyVar,session,effect,modal}` — Reducible at each of the
  10 SN-direct Ty arms is closed under raw `parProgress` reduction.
  Each closure unfolds definitionally to `Term.isStronglyNormalizing`
  → `RawTerm.isStronglyNormalizing _.toRaw`, so the body is a
  one-line application of K12.20.B's raw `step_preserves`.  Signature
  uses raw step `RawStep.parProgress sourceRaw targetRaw` (not typed
  Step) because SN unfolds to raw SN, bypassing the typed Step
  relation entirely — keeps K12.20.D zero-dep on typed Step's
  cascade infrastructure.
  Each lemma's audit pin verifies the typed lift inherits raw
  step_preserves's zero-axiom status.

K12.20.E ships (typed neutral-var reducibility at SN-direct arms):
* `Term.isStronglyNormalizing_of_varShape` — universal SN of any
  Term whose raw projection is `RawTerm.var position`.  Foundation
  for the cascade where var-shaped Terms (canonical Term.var OR
  `▸`-cast forms with same raw index) need to be exhibited SN.
  Definitional unfolding chain: Term.SN → raw SN at term.toRaw =
  RawTerm.var position → K12.20.C's `var_isStronglyNormalizing`.
* `Reducible.{unit,bool,nat,empty,interval,universe,tyVar,session,
  effect,modal}_of_varShape` — variables are reducible at each of
  the 10 SN-direct Ty arms.  Each body is
  `Term.isStronglyNormalizing_of_varShape term`; lifts through
  Reducible's SN-direct unfolding.
  These 11 theorems are the typed-level "every variable is reducible
  at an SN-direct binding type" base, foundational for
  ReducibleSubst.identity (where every position's TermSubst value is
  the canonical Term.var) and ReducibleSubst.singleton's k+1-positions
  case (where the TermSubst supplies a cast-Term.var at the
  weaken-substituted-out type).  Compound-arm neutral-reducibility
  (var reducible at arrow/Σ/...) needs full CR3 / outer Ty induction;
  ships in K12.20.G.

K12.20.F ships (typed CR2 lift — arrow compound arm):
* `Reducible.step_preserves_arrow` — Reducible at `Ty.arrow A B`
  is closed under raw `parProgress`.  Takes `codomainCR2` as an
  explicit hypothesis (the recursive ingredient: CR2 at codomain).
  Body: refine into the pair conjunct, dispatch SN-preservation
  through K12.20.B's raw `step_preserves`, dispatch closure-
  preservation through codomainCR2 with raw app-cong + refl on the
  unchanged arg.  Distinctness of `app source arg ≠ app target arg`
  is discharged by `injection` (ctor injectivity at RawTerm.app —
  propext-free in Lean 4 core).
  First compound-arm CR2; remaining 14 (piTy/Σ/id/list/option/either/
  path/glue/oeq/idStrict/equiv/refine/record/codata) follow the same
  shape and ship in K12.20.G+.  The combined structurally-recursive
  `Reducible.step_preserves` bundling all 25 arms ships in K12.20.H.

K12.20.G ships (typed CR2 lift — piTy weak-closure compound arm):
* `Reducible.step_preserves_piTy` — Reducible at `Ty.piTy A B` is
  closed under raw `parProgress`.  Unlike arrow, piTy's K12.6
  closure is WEAK: eliminator output is `SN(appPi f arg)` not full
  `Reducible codomain (appPi f arg)`.  Consequence: NO codomainCR2
  hypothesis needed — both SN-of-functionTerm and SN-of-appPi-result
  are discharged by K12.20.B's raw `step_preserves` directly.
  Term.appPi shares the same raw form (`RawTerm.app f a`) as
  Term.app, so the raw `RawStep.par.app` cong rule applies
  identically; distinctness via `injection` on RawTerm.app.

K12.20.H ships (typed CR2 lift — sigmaTy asymmetric-closure compound arm):
* `Reducible.step_preserves_sigmaTy` — Reducible at
  `Ty.sigmaTy A B` is closed under raw `parProgress`.  K12.7's
  asymmetric closure has three conjuncts: SN(pair) + Reducible A
  (fst pair) + SN(snd pair).  Each preservation discharged
  independently: SN conjuncts via K12.20.B's raw `step_preserves`
  on fst/snd-cong; the middle full-Reducible conjunct uses an
  explicit `firstTypeCR2` hypothesis (mirrors K12.20.F arrow
  parameterization) lifted through `RawStep.par.fst` cong.
  Distinctness on fst/snd via `injection` on RawTerm.fst.injEq /
  RawTerm.snd.injEq (ctor injectivity, propext-free).  Third
  compound-arm CR2; 12 remaining (id/list/option/either/path/
  glue/oeq/idStrict/equiv/refine/record/codata) follow the same
  per-arm decomposition pattern.

K12.20.I ships (typed CR2 lift — id weak-idJ-closure compound arm):
* `Reducible.step_preserves_id` — Reducible at
  `Ty.id A x y` is closed under raw `parProgress`.  K12.9's weak
  idJ closure has two conjuncts: SN(witness) + (∀ motiveType
  baseCase, SN(baseCase) → SN(idJ baseCase witness)).  Both are
  pure-SN preservation — the eliminator output is plain SN, not
  full Reducible, so NO recursive motiveTypeCR2 hypothesis is
  needed (full Tait dep-J closure deferred to Kripke logical
  relation refactor).  Same weak-closure pattern as K12.20.G
  piTy.  Term.idJ shares raw form `RawTerm.idJ baseRaw witnessRaw`
  (per Term.lean:245); `RawStep.par.idJ` takes paired par steps
  on baseRaw + witnessRaw, so the baseRaw side gets `par.refl`
  while witness side gets `rawStep.1`.  Fourth compound-arm CR2;
  11 remaining (list/option/either/path/glue/oeq/idStrict/equiv/
  refine/record/codata).

K12.20.J ships (typed CR2 lift — listType weak-elim-closure compound arm):
* `Reducible.step_preserves_listType` — Reducible at
  `Ty.listType A` is closed under raw `parProgress`.  K12.8's
  weak elim closure has two conjuncts: SN(listTerm) + (∀ M
  nilBranch consBranch, SN nilBranch → cons-applied-closure →
  SN(listElim listTerm nilBranch consBranch)).  The hypothesis
  chain inside the second conjunct (Reducible elementType head +
  SN tail → SN(consBranch head tail)) propagates unchanged
  through sourceReducible.2 — CR2 needs NO recursive
  elementTypeCR2 hypothesis because eliminator output is plain
  SN.  Same weak-closure pattern as K12.20.G piTy and K12.20.I
  id.  Term.listElim raw form is `RawTerm.listElim scrutineeRaw
  nilRaw consRaw` (per Term.lean:200); `RawStep.par.listElim`
  takes triple par steps (per RawPar.lean:120) — for CR2 the
  branches use `par.refl` while scrutinee gets `rawStep.1`.
  Fifth compound-arm CR2; 10 remaining (option/either/path/glue/
  oeq/idStrict/equiv/refine/record/codata).

K12.20.K ships (typed CR2 lift — optionType weak-elim-closure compound arm):
* `Reducible.step_preserves_optionType` — Reducible at
  `Ty.optionType A` is closed under raw `parProgress`.  K12.8's
  optionType arm is the cleanest of the three K12.8 parametric
  inductives: someBranch's type matches K12.6 piTy weak shape
  exactly.  Closure: SN(optionTerm) + (∀ M noneBranch someBranch,
  SN noneBranch → ∀ v, Reducible A v → SN(some-app v) →
  SN(optionMatch optionTerm noneBranch someBranch)).  Same
  mechanical shape as K12.20.J listType — Term.optionMatch raw
  form is `RawTerm.optionMatch scrutineeRaw noneRaw someRaw`
  (per Term.lean:216); `RawStep.par.optionMatch` takes triple
  par steps (per RawPar.lean:136).  Sixth compound-arm CR2;
  9 remaining (either/path/glue/oeq/idStrict/equiv/refine/
  record/codata).

K12.20.L ships (typed CR2 lift — eitherType symmetric-weak-elim-closure compound arm):
* `Reducible.step_preserves_eitherType` — Reducible at
  `Ty.eitherType A B` is closed under raw `parProgress`.
  K12.8's eitherType arm is **symmetric**: both leftType and
  rightType are strict sub-Ty of `Ty.eitherType leftType
  rightType`, each branch's arrow shape matches K12.6 piTy weak
  closure per side.  Closure: SN(eitherTerm) + (∀ M leftBranch
  rightBranch, left-applied-closure → right-applied-closure →
  SN(eitherMatch eitherTerm leftBranch rightBranch)).  Both
  hypothesis chains propagate unchanged through sourceReducible.2
  — NO recursive leftTypeCR2/rightTypeCR2 hypothesis needed
  (eliminator output is plain SN).  Term.eitherMatch raw form is
  `RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw` (per
  Term.lean:234); `RawStep.par.eitherMatch` takes triple par
  steps (per RawPar.lean:159).  Seventh compound-arm CR2;
  8 remaining (path/glue/oeq/idStrict/equiv/refine/record/codata).
  Closes the K12.8 parametric-inductive triple (list/option/
  either) at the typed CR2 layer.

K12.20-K12.26 will ship the remaining fundamental-lemma cases (lam,
β-redexes, ι-recursors, HOTT, cubical, modal, cumul/refine/type-
code).  K12.27 closes M04 / `strong_normalization`. -/

#print axioms RawStep.parProgress
#print axioms RawTerm.isStronglyNormalizing
#print axioms Term.isStronglyNormalizing
#print axioms Reducible
#print axioms Reducible.isStronglyNormalizing
#print axioms ReducibleSubst
#print axioms Reducible.fundamental_var
#print axioms RawTerm.unit_isStronglyNormalizing
#print axioms RawTerm.boolTrue_isStronglyNormalizing
#print axioms RawTerm.boolFalse_isStronglyNormalizing
#print axioms RawTerm.natZero_isStronglyNormalizing
#print axioms Reducible.fundamental_unit
#print axioms Reducible.fundamental_boolTrue
#print axioms Reducible.fundamental_boolFalse
#print axioms Reducible.fundamental_natZero
#print axioms RawTerm.lam_isStronglyNormalizing
#print axioms RawTerm.isStronglyNormalizing.step_preserves
#print axioms RawTerm.var_isStronglyNormalizing
#print axioms RawTerm.natSucc_isStronglyNormalizing
#print axioms Reducible.step_preserves_unit
#print axioms Reducible.step_preserves_bool
#print axioms Reducible.step_preserves_nat
#print axioms Reducible.step_preserves_empty
#print axioms Reducible.step_preserves_interval
#print axioms Reducible.step_preserves_universe
#print axioms Reducible.step_preserves_tyVar
#print axioms Reducible.step_preserves_session
#print axioms Reducible.step_preserves_effect
#print axioms Reducible.step_preserves_modal
#print axioms Term.isStronglyNormalizing_of_varShape
#print axioms Reducible.unit_of_varShape
#print axioms Reducible.bool_of_varShape
#print axioms Reducible.nat_of_varShape
#print axioms Reducible.empty_of_varShape
#print axioms Reducible.interval_of_varShape
#print axioms Reducible.universe_of_varShape
#print axioms Reducible.tyVar_of_varShape
#print axioms Reducible.session_of_varShape
#print axioms Reducible.effect_of_varShape
#print axioms Reducible.modal_of_varShape
#print axioms Reducible.step_preserves_arrow
#print axioms Reducible.step_preserves_piTy
#print axioms Reducible.step_preserves_sigmaTy
#print axioms Reducible.step_preserves_id
#print axioms Reducible.step_preserves_listType
#print axioms Reducible.step_preserves_optionType
#print axioms Reducible.step_preserves_eitherType

end LeanFX2.Smoke
