import FX1Poly.Core.RawTerm

/-! # Foundation/PolyCell/Core/NeutralTerm — the concrete neutral predicate

A **neutral** raw term is one that is stuck at the root: it is neither a
canonical constructor nor a redex, so no root reduction can fire.  Concretely
it is a variable, or an elimination form whose *principal* (scrutinee) child is
itself neutral — the eliminator cannot ι-fire because its scrutinee never
reaches a constructor.

This predicate is the foundation for the Tait reducibility candidate
machinery (polycell.md §11.8.5 P-sequence).  A reducibility candidate is a
set of strongly-normalizing terms closed under the three CR conditions, and
CR3 — "a neutral term all of whose one-step reducts are reducible is itself
reducible" — is stated over *neutrals*.  `StrongNormalizationNeutral.lean`
carries neutrality as an abstract `isNeutralHead : RawTerm scope → Prop`
parameter; this file provides the concrete inductive that those generic
lemmas are instantiated at.

## Grounding: the arms are the elimination forms

The arms are read directly off the authoritative ι-rule enumeration in
`Step.lean` (the 16 `iota*` constructors) plus β (`gen_app` on a `gen_lam`
head).  The complete current-substrate elimination set is

  app · fst · snd · boolElim · natElim · natRec · listElim · optionMatch
  · eitherMatch · idJ · idStrictRec

with the *principal* child (the one whose canonical form triggers the rule)
being child 0 for every form except `idJ`/`idStrictRec`, whose principal child
is the identity *witness* (child 1; the base case is passive).

Because FX's ι-rules are Church-encoded — all binding is deferred to the
app-chain *reduct* (`natElim (succ n) z s ↝ app (app s n) (natElim n z s)`),
never carried on the eliminator's own children — every eliminator child lives
at the ambient `scope`.  So each arm's children are plain `RawTerm scope`, with
no binder-shift arithmetic.

## Scope boundary (honesty)

Only the eliminators that *have* an ι-rule in the current substrate form
neutrals.  The cubical (`transp`/`hcomp`/`unglue`), modal (`modElim`), clock
(`force`), and parametric (`paramApp`) eliminators have no ι-rule yet, hence
form no neutrals yet; this inductive gains an arm per eliminator as each
lands.  The definition is therefore complete *for the current substrate*,
not over-claimed against future generators.

## Zero-axiom verification

A plain inductive-family declaration — no match compilation, no `propext` /
`Quot.sound`.  Swept by `#audit_namespace FX1Poly.Core` in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

/-- `IsNeutral t` holds when `t` is stuck at the root: a variable, or an
elimination form whose principal child is neutral.  One arm per current
elimination form; see the file header for the grounding against `Step.lean`'s
ι-rules. -/
inductive IsNeutral : {scope : Nat} → RawTerm scope → Prop where
  /-- A variable is the atomic neutral. -/
  | var {scope : Nat} (index : Fin scope) :
      IsNeutral (.mkGen .gen_var index .childNil)
  /-- Application is neutral when its function head is neutral — β cannot fire
  because the head never reaches a `gen_lam`. -/
  | app {scope : Nat} {head argument : RawTerm scope}
      (headIsNeutral : IsNeutral head) :
      IsNeutral (.mkGen .gen_app ()
        (.childCons head (.childCons argument .childNil)))
  /-- First projection is neutral when its argument is neutral. -/
  | fst {scope : Nat} {argument : RawTerm scope}
      (argumentIsNeutral : IsNeutral argument) :
      IsNeutral (.mkGen .gen_fst () (.childCons argument .childNil))
  /-- Second projection is neutral when its argument is neutral. -/
  | snd {scope : Nat} {argument : RawTerm scope}
      (argumentIsNeutral : IsNeutral argument) :
      IsNeutral (.mkGen .gen_snd () (.childCons argument .childNil))
  /-- Boolean elimination is neutral when its scrutinee is neutral. -/
  | boolElim {scope : Nat} {scrutinee thenBranch elseBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_boolElim ()
        (.childCons scrutinee
          (.childCons thenBranch (.childCons elseBranch .childNil))))
  /-- Natural-number elimination is neutral when its scrutinee is neutral. -/
  | natElim {scope : Nat} {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_natElim ()
        (.childCons scrutinee
          (.childCons zeroBranch (.childCons succBranch .childNil))))
  /-- Natural-number recursion is neutral when its scrutinee is neutral. -/
  | natRec {scope : Nat} {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_natRec ()
        (.childCons scrutinee
          (.childCons zeroBranch (.childCons succBranch .childNil))))
  /-- List elimination is neutral when its scrutinee is neutral. -/
  | listElim {scope : Nat} {scrutinee nilBranch consBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_listElim ()
        (.childCons scrutinee
          (.childCons nilBranch (.childCons consBranch .childNil))))
  /-- Option matching is neutral when its scrutinee is neutral. -/
  | optionMatch {scope : Nat}
      {scrutinee noneBranch someBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_optionMatch ()
        (.childCons scrutinee
          (.childCons noneBranch (.childCons someBranch .childNil))))
  /-- Either matching is neutral when its scrutinee is neutral. -/
  | eitherMatch {scope : Nat}
      {scrutinee leftBranch rightBranch : RawTerm scope}
      (scrutineeIsNeutral : IsNeutral scrutinee) :
      IsNeutral (.mkGen .gen_eitherMatch ()
        (.childCons scrutinee
          (.childCons leftBranch (.childCons rightBranch .childNil))))
  /-- Identity-type elimination is neutral when its witness is neutral; the
  base case is passive, so it places no neutrality demand. -/
  | idJ {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : IsNeutral witness) :
      IsNeutral (.mkGen .gen_idJ ()
        (.childCons baseCase (.childCons witness .childNil)))
  /-- Strict identity elimination is neutral when its witness is neutral.
  Identical child spine to `idJ`. -/
  | idStrictRec {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : IsNeutral witness) :
      IsNeutral (.mkGen .gen_idStrictRec ()
        (.childCons baseCase (.childCons witness .childNil)))

/-- **A neutral term forces an inhabitant of its scope's variable space.**  Every `IsNeutral` derivation
bottoms out at the atomic `var` arm — a `Fin scope` index — and every other arm is rooted at an eliminator
whose neutral premise lives at the SAME scope.  So a neutral term cannot exist when `Fin scope` is empty:
threading the emptiness witness down the neutral spine reaches the head variable and refutes it.  Stated
scope-polymorphically (`(Fin scope → False) → False`) so the induction motive stays index-clean — no scope is
fixed in the motive, every recursive arm just forwards the same emptiness witness to its inductive
hypothesis. -/
theorem IsNeutral.elimEmptyScope {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : (Fin scope → False) → False := by
  induction neutral with
  | var index => intro scopeEmpty; exact scopeEmpty index
  | app _ headInductiveHypothesis => intro scopeEmpty; exact headInductiveHypothesis scopeEmpty
  | fst _ argumentInductiveHypothesis => intro scopeEmpty; exact argumentInductiveHypothesis scopeEmpty
  | snd _ argumentInductiveHypothesis => intro scopeEmpty; exact argumentInductiveHypothesis scopeEmpty
  | boolElim _ scrutineeInductiveHypothesis => intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | natElim _ scrutineeInductiveHypothesis => intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | natRec _ scrutineeInductiveHypothesis => intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | listElim _ scrutineeInductiveHypothesis => intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | optionMatch _ scrutineeInductiveHypothesis =>
      intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | eitherMatch _ scrutineeInductiveHypothesis =>
      intro scopeEmpty; exact scrutineeInductiveHypothesis scopeEmpty
  | idJ _ witnessInductiveHypothesis => intro scopeEmpty; exact witnessInductiveHypothesis scopeEmpty
  | idStrictRec _ witnessInductiveHypothesis => intro scopeEmpty; exact witnessInductiveHypothesis scopeEmpty

/-- **No closed term is neutral.**  A `RawTerm 0` (the empty scope) cannot be neutral: `Fin 0` is empty, so
`IsNeutral.elimEmptyScope` refutes the neutral spine at its head variable.  This is the closed-canonical-forms
precursor for canonicity and consistency: a CLOSED normal form is never a stuck (neutral) eliminator, so it
must be an introduction form — and the empty type, having no introduction form, has no closed inhabitant. -/
theorem IsNeutral.noClosed {term : RawTerm 0} (neutral : IsNeutral term) : False :=
  neutral.elimEmptyScope (fun index => index.elim0)

end FX1Poly.Core
