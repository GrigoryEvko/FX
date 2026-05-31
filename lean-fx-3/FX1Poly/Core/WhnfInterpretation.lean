import FX1Poly.Core.CandidateInterpretation
import FX1Poly.Core.HeadStep

/-! # Foundation/PolyCell/Core/WhnfInterpretation
    — the weak-head-dispatching reducibility interpretation (conversion-invariant)

The shipped `InterpretsType` (`CandidateInterpretation`) dispatches on the **syntactic head**: its
`baseType` arm fires for any code whose root generator is neither `gen_var` nor `gen_piTyCode`, and
assigns it the strong-normalization candidate.  That is sound for type-codes already in weak-head
normal form, but it BREAKS conversion-invariance: a redex-type `app (lam codomainCode) argument`
has root `gen_app`, so `InterpretsType` collapses it to the SN candidate — even when its β-contractum
is a Π-code that should denote an ARROW candidate.  The fundamental theorem's `conv` arm (classifier
related by `Conv`, which contracts such redexes) cannot then transport reducibility.

This file builds the FIX: a **weak-head-dispatching** interpretation `InterpretsWhnf`, closed under
head-expansion by construction.  Its arms:

  * `typeVariable` — a type variable interprets to its environment candidate (as before);
  * `piType` — a Π-code interprets to the arrow candidate of its children's interpretations (codomain
    in the extended environment), as before;
  * `baseNormal` — a code whose root is neither `gen_var`, `gen_piTyCode`, NOR `gen_app` interprets to
    the SN candidate.  `gen_app` is excluded because it is the only weak-head-reducible head; every
    `gen_app`-headed code is handled by `neutralApp` or `headExpand`;
  * `neutralApp` — a `gen_app`-headed code with NO weak-head step (a neutral application, its function
    never a λ) interprets to the SN candidate;
  * `headExpand` — if `typeCode` weak-head reduces to `reduct` and `reduct` interprets to a candidate,
    then `typeCode` interprets to the SAME candidate.  This is what makes the relation
    conversion-invariant: a redex inherits its contractum's candidate.

Because `HeadStep` is DETERMINISTIC (`HeadStep.deterministic`, no confluence needed), this relation
stays functional — the determinism proof (next brick) inverts the second derivation against the
first's unique weak-head reduct.

This brick: the inductive plus `InterpretsWhnf.isReducibilityCandidate` — every interpreted code is a
genuine Girard reducibility candidate.  The `headExpand` arm propagates the candidate UNCHANGED, so it
just forwards the induction hypothesis; the other arms reuse the shipped candidate combinators.

## Additive

`InterpretsType` and all its lemmas stay shipped and untouched.  `InterpretsWhnf` is a new relation
built ALONGSIDE it, sharing the candidate-environment infrastructure (`CandidateEnv`, `IsCandidateEnv`,
`isCandidateEnv_cons`).

## Zero-axiom verification

A plain inductive `Prop` (indexed by the candidate predicate) + induction discharging to the shipped
candidate combinators (`isArrowReducible_isReducibilityCandidate`,
`isStronglyNormalizing_isReducibilityCandidate`, `containsVariable`).  `Fin` positions split by the
blessed `⟨0, _⟩` / `⟨k + 1, _⟩` match.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- The weak-head-dispatching reducibility interpretation.  A type-code denotes a reducibility
candidate under an environment, dispatching AFTER weak-head reduction: a redex-headed code inherits
its contractum's candidate via `headExpand`, so the relation is conversion-invariant where
`InterpretsType` (syntactic-head dispatch) is not.  Type variables look up the environment; a Π-code
denotes the arrow candidate; a weak-head-normal non-variable / non-Π code denotes the SN candidate
(via `baseNormal` for a non-application head, `neutralApp` for a stuck application). -/
inductive InterpretsWhnf {targetScope : Nat} :
    {scope : Nat} → CandidateEnv scope targetScope → RawTerm scope →
      (RawTerm targetScope → Prop) → Prop where
  /-- A type variable interprets to its environment candidate. -/
  | typeVariable {scope : Nat} (env : CandidateEnv scope targetScope) (index : Fin scope) :
      InterpretsWhnf env (.mkGen .gen_var index .childNil) (env index)
  /-- A Π-type code interprets to the arrow candidate; the codomain is interpreted in the environment
  extended by the domain's candidate. -/
  | piType {scope : Nat} {env : CandidateEnv scope targetScope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate codomainCandidate : RawTerm targetScope → Prop} :
      InterpretsWhnf env domainCode domainCandidate →
      InterpretsWhnf (env.cons domainCandidate) codomainCode codomainCandidate →
      InterpretsWhnf env
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons codomainCode .childNil)))
        (IsArrowReducible domainCandidate codomainCandidate)
  /-- A weak-head-normal code whose root is neither a variable, a Π, NOR an application interprets to
  the SN candidate.  Excluding `gen_app` is what keeps the relation deterministic: the application head
  is the only weak-head-reducible head, so it is routed through `neutralApp` / `headExpand` instead. -/
  | baseNormal {scope : Nat} (env : CandidateEnv scope targetScope) {term : RawTerm scope} :
      term.rootGenerator ≠ Generator.gen_var →
      term.rootGenerator ≠ Generator.gen_piTyCode →
      term.rootGenerator ≠ Generator.gen_app →
      InterpretsWhnf env term IsStronglyNormalizing
  /-- A `gen_app`-headed code with NO weak-head step (a stuck/neutral application — its function
  position never reaches a λ) interprets to the SN candidate. -/
  | neutralApp {scope : Nat} (env : CandidateEnv scope targetScope)
      {functionTerm argument : RawTerm scope} :
      (∀ reduct : RawTerm scope,
        ¬ HeadStep
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) reduct) →
      InterpretsWhnf env
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
        IsStronglyNormalizing
  /-- A redex-headed code inherits the candidate of its weak-head reduct.  This is the
  conversion-invariance arm: `app (lam codomainCode) argument` denotes whatever its β-contractum
  denotes. -/
  | headExpand {scope : Nat} {env : CandidateEnv scope targetScope}
      {typeCode reduct : RawTerm scope} {candidate : RawTerm targetScope → Prop} :
      HeadStep typeCode reduct →
      InterpretsWhnf env reduct candidate →
      InterpretsWhnf env typeCode candidate

/-- **Every weak-head-interpreted type-code is a reducibility candidate**, given a well-formed
environment.  Induction on the interpretation: a type variable's candidate comes from the environment;
the SN candidate (`baseNormal` / `neutralApp`) is shipped; the arrow candidate is a candidate by
`isArrowReducible_isReducibilityCandidate` (CR1 inhabitedness discharged by variable 0); and
`headExpand` forwards its induction hypothesis unchanged — the candidate is the SAME predicate as the
contractum's, so candidate-hood transports verbatim.  This is what makes the interpretation meaningful:
an interpreted type is a real candidate, so the fundamental theorem extracts SN from membership. -/
theorem InterpretsWhnf.isReducibilityCandidate {targetScopePred scope : Nat}
    {env : CandidateEnv scope (targetScopePred + 1)} {typeCode : RawTerm scope}
    {candidate : RawTerm (targetScopePred + 1) → Prop}
    (interprets : InterpretsWhnf env typeCode candidate) :
    IsCandidateEnv env → IsReducibilityCandidate candidate := by
  induction interprets with
  | typeVariable environment index =>
      intro envIsCandidate
      exact envIsCandidate index
  | piType _domainInterprets _codomainInterprets domainInductiveHypothesis
      codomainInductiveHypothesis =>
      intro envIsCandidate
      have domainCandidate := domainInductiveHypothesis envIsCandidate
      have codomainCandidate :=
        codomainInductiveHypothesis (isCandidateEnv_cons domainCandidate envIsCandidate)
      exact isArrowReducible_isReducibilityCandidate domainCandidate codomainCandidate
        (.mkGen .gen_var ⟨0, Nat.zero_lt_succ targetScopePred⟩ .childNil)
        (domainCandidate.containsVariable ⟨0, Nat.zero_lt_succ targetScopePred⟩)
  | baseNormal environment _notVariable _notPiType _notApp =>
      intro _envIsCandidate
      exact isStronglyNormalizing_isReducibilityCandidate
  | neutralApp environment _noHeadStep =>
      intro _envIsCandidate
      exact isStronglyNormalizing_isReducibilityCandidate
  | headExpand _headStep _reductInterprets reductInductiveHypothesis =>
      intro envIsCandidate
      exact reductInductiveHypothesis envIsCandidate

end FX1Poly.Core
