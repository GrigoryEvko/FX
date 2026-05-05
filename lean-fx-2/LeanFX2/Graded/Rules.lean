import LeanFX2.Graded.Ctx
import LeanFX2.Graded.GradeVector

/-! # Graded/Rules — graded MLTT typing rules

Implements the graded MLTT calculus per `fx_design.md` §6.2, with
**Wood/Atkey 2022 corrected Lam rule** at the centre.

## Core judgment

```
WellGraded gradedCtx attribution
```

A term-shaped grade attribution that records, per binding in
`gradedCtx`, how a candidate term USES that binding across all
registered dimensions.  The attribution is encoded as a recursive
Type (Unit for empty, GradeVector × tail for cons) — same encoding
as `GradeVector` — because the indexed-inductive alternative leaks
propext through partial-pattern equation lemmas (cf. memory:
indexed-inductive partial-match trap).

## Rules

* **Var** (§6.2): `Γ, x :_r A |- x : A`, attribution `singleton x`
* **App** (§6.2): `Γ |-_p1 f, Γ |-_p2 a → Γ |-_(p1 + r * p2) f a`
  where `r` is `f`'s parameter grade.  Attributions add pointwise
  with the argument's attribution scaled by `r`.
* **Lam (Wood/Atkey 2022)** (§6.2): `Γ/p, x :_r A |-_1 b : B →
  Γ |-_p (fn(x) => b) : (x :_r A) -> B`.  Captured by the
  `IsLamCompatible` predicate: the body's attribution at the new
  binding must equal `paramGrade`, and the inherited bindings'
  grades must be exactly `closureGrade .scaleBy lamAttr` for
  some uniquely-determined `lamAttr`.  Existence of `lamAttr` IS
  the context division.
* **Let** (§6.2): `Γ |-_p1 e, Γ, x :_r A |-_p2 body →
  Γ |-_(r * p1 + p2) (let x = e; body)`.  Same structure as App
  but with let-binding semantics.
* **If**: branches' attributions JOIN (worst-case via pointwise
  addition; usage-semiring's `1+1 = ω` makes a linear binding
  used in both branches type-error).
* **Subsumption**: weaken attribution `attr1 ≤ attr2` to use
  more-permissive grades where less-permissive accepted.

## Why context division as existential

The Wood/Atkey 2022 division `pi/p = max { d : d * p ≤ pi }`
requires a `Decidable` preorder + a `divide` operation.  Rather
than committing to a global `divide` typeclass field (which
would interlock with all 21 dimension instances), we phrase
the Lam rule as: ∃ lamAttr, bodyAttr = (paramGrade, lamAttr.scaleBy
closureGrade).  The witness `lamAttr` IS the divided context,
and its existence captures the maximality condition implicitly.

## Why recursive Type, not indexed inductive

`GradeAttribution dims scope` could be a `Nat`-indexed inductive
(empty at 0, cons at scope+1).  But Lean 4's match compiler
emits `propext` through equation lemmas when partial-matching
indexed inductives at restricted indices (cf. memory:
`feedback_lean_indexed_partial_match.md`).  The recursive-Type
form (Unit at 0, Prod at scope+1) avoids this entirely — pattern
matching on the underlying Unit/Prod is propext-clean, matching
the proven approach used in `GradeVector`.

## Dependencies

* `Graded/Ctx.lean` — graded contexts
* `Graded/GradeVector.lean` — pointwise grade vectors
* `Graded/Semiring.lean` (transitive) — semiring framework

## Downstream

* `Algo/Check.lean` — bidirectional checker uses graded rules
* `Algo/Soundness.lean` — soundness theorem against graded rules
* `Graded/AtkeyAttack.lean` — verifies the Wood/Atkey 2022
  correction rejects Atkey 2018's broken closure capture

Zero-axiom verified per declaration via AuditAll. -/

namespace LeanFX2.Graded

/-! ## GradeAttribution: per-binding usage profile

A `GradeAttribution dims scope` records one `GradeVector dims` per
binding in scope.  Recursive Type — `Unit` at scope 0, `GradeVector
dims × GradeAttribution dims scope` at scope+1.

The attribution captures the term-shaped ANSWER to "how does this
term use each binding?".  The Lam rule's context division operates
on the tail of an attribution, dividing each binding's grade
vector by the closure's multiplicity grade. -/

/-- Per-binding grade attribution: recursive Type, length-indexed
by `scope`.  Position 0 (the head of the pair) is the most-
recently-bound variable; the tail covers inherited bindings. -/
def GradeAttribution (dims : List Dimension) : Nat → Type
  | 0          => Unit
  | scope + 1  => GradeVector dims × GradeAttribution dims scope

namespace GradeAttribution

variable {dims : List Dimension}

/-! ## Constants and basic operations -/

/-- The all-zero attribution: every binding has GradeVector.zero
usage.  Built by structural recursion on the scope. -/
def zero : ∀ {scope : Nat}, GradeAttribution dims scope
  | 0     => ()
  | _ + 1 => (GradeVector.zero, zero)

/-- The unit-grade attribution at the head, zero on the tail.
At scope+1, this represents "the most-recently-bound variable
is used at unit grade, no inherited binding is touched". -/
def unitHead : ∀ {scope : Nat}, GradeAttribution dims (scope + 1)
  | _ => (GradeVector.one, zero)

/-- Pointwise addition: every binding's grade vector adds with
the corresponding binding's vector in the second attribution.
Matches on Nat scope (propext-clean — cf. GradeVector.add). -/
def add : ∀ {scope : Nat},
    GradeAttribution dims scope →
    GradeAttribution dims scope →
    GradeAttribution dims scope
  | 0,     _,            _            => ()
  | _ + 1, (firstHead, firstTail), (secondHead, secondTail) =>
      (GradeVector.add firstHead secondHead,
       add firstTail secondTail)

/-- Scale every binding's grade vector by a fixed grade vector
(scalar pointwise multiplication). -/
def scaleBy : ∀ {scope : Nat},
    GradeVector dims →
    GradeAttribution dims scope →
    GradeAttribution dims scope
  | 0,     _,         _                       => ()
  | _ + 1, scalarVec, (headValue, innerTail)  =>
      (GradeVector.mul scalarVec headValue,
       scaleBy scalarVec innerTail)

/-- The singleton attribution: position `varPos` has grade
`GradeVector.one`, all other positions have `GradeVector.zero`.
Implements the Var rule's "grade `r` at x, 0 elsewhere" with
`r = 1`; non-unit grades are obtained via `scaleBy`. -/
def singleton : ∀ {scope : Nat}, Fin scope → GradeAttribution dims scope
  | 0,     ⟨_, isLt⟩ => absurd isLt (Nat.not_lt_zero _)
  | _ + 1, ⟨0, _⟩    => (GradeVector.one, zero)
  | _ + 1, ⟨innerVal + 1, isLt⟩ =>
      (GradeVector.zero,
       singleton ⟨innerVal, Nat.lt_of_succ_lt_succ isLt⟩)

/-- Pointwise preorder: every binding's grade vector is `≤` the
corresponding binding's vector in the second attribution. -/
def le : ∀ {scope : Nat},
    GradeAttribution dims scope →
    GradeAttribution dims scope →
    Prop
  | 0,     _,            _            => True
  | _ + 1, (firstHead, firstTail), (secondHead, secondTail) =>
      GradeVector.le firstHead secondHead ∧ le firstTail secondTail

/-! ## Algebraic laws

Each law lifts the corresponding GradeVector law pointwise.
Proofs by structural recursion on the scope.  All proofs follow
the same pattern as `GradeVector` — pair-equality from
componentwise equalities. -/

/-- Pointwise addition is left-identity in zero. -/
theorem add_zero_left :
    ∀ {scope : Nat} (someAttr : GradeAttribution dims scope),
      add zero someAttr = someAttr
  | 0,     ()                  => rfl
  | _ + 1, (headValue, innerTail) =>
      prodMkEq
        (GradeVector.add_zero_left headValue)
        (add_zero_left innerTail)

/-- Pointwise addition is right-identity in zero. -/
theorem add_zero_right :
    ∀ {scope : Nat} (someAttr : GradeAttribution dims scope),
      add someAttr zero = someAttr
  | 0,     ()                  => rfl
  | _ + 1, (headValue, innerTail) =>
      prodMkEq
        (GradeVector.add_zero_right headValue)
        (add_zero_right innerTail)

/-- Pointwise addition is commutative.  Lifted from
`GradeVector.add_comm` componentwise. -/
theorem add_comm :
    ∀ {scope : Nat}
      (firstAttr secondAttr : GradeAttribution dims scope),
      add firstAttr secondAttr = add secondAttr firstAttr
  | 0,     _, _ => rfl
  | _ + 1, (firstHead, firstTail), (secondHead, secondTail) =>
      prodMkEq
        (GradeVector.add_comm firstHead secondHead)
        (add_comm firstTail secondTail)

/-- Pointwise addition is associative. -/
theorem add_assoc :
    ∀ {scope : Nat}
      (firstAttr secondAttr thirdAttr : GradeAttribution dims scope),
      add (add firstAttr secondAttr) thirdAttr =
        add firstAttr (add secondAttr thirdAttr)
  | 0,     _, _, _ => rfl
  | _ + 1,
    (firstHead, firstTail),
    (secondHead, secondTail),
    (thirdHead, thirdTail) =>
      prodMkEq
        (GradeVector.add_assoc firstHead secondHead thirdHead)
        (add_assoc firstTail secondTail thirdTail)

/-- Scaling-by-zero collapses any attribution to zero.  Lifted
from `GradeVector.mul_zero_left` componentwise. -/
theorem scaleBy_zero_scalar :
    ∀ {scope : Nat} (someAttr : GradeAttribution dims scope),
      scaleBy GradeVector.zero someAttr = zero
  | 0,     ()                   => rfl
  | _ + 1, (headValue, innerTail) =>
      prodMkEq
        (GradeVector.mul_zero_left headValue)
        (scaleBy_zero_scalar innerTail)

/-- Scaling the zero attribution by any scalar gives zero.
Dual to `scaleBy_zero_scalar`: there it's the scalar that's
zero; here it's the attribution.  Lifted from
`GradeVector.mul_zero_right`. -/
theorem scaleBy_zero_attr :
    ∀ {scope : Nat} (scalarVec : GradeVector dims),
      scaleBy scalarVec (zero : GradeAttribution dims scope) = zero
  | 0,     _ => rfl
  | _ + 1, scalarVec =>
      prodMkEq
        (GradeVector.mul_zero_right scalarVec)
        (scaleBy_zero_attr scalarVec)

/-- Scaling by one is identity.  Lifted from
`GradeVector.mul_one_left`. -/
theorem scaleBy_one_scalar :
    ∀ {scope : Nat} (someAttr : GradeAttribution dims scope),
      scaleBy GradeVector.one someAttr = someAttr
  | 0,     ()                   => rfl
  | _ + 1, (headValue, innerTail) =>
      prodMkEq
        (GradeVector.mul_one_left headValue)
        (scaleBy_one_scalar innerTail)

/-- Pointwise preorder is reflexive. -/
theorem le_refl :
    ∀ {scope : Nat} (someAttr : GradeAttribution dims scope),
      le someAttr someAttr
  | 0,     ()                   => True.intro
  | _ + 1, (headValue, innerTail) =>
      ⟨GradeVector.le_refl headValue, le_refl innerTail⟩

/-- Pointwise preorder is transitive. -/
theorem le_trans :
    ∀ {scope : Nat}
      (firstAttr secondAttr thirdAttr : GradeAttribution dims scope),
      le firstAttr secondAttr → le secondAttr thirdAttr →
      le firstAttr thirdAttr
  | 0, _, _, _, _, _ => True.intro
  | _ + 1,
    (firstHead, firstTail), (secondHead, secondTail), (thirdHead, thirdTail),
    ⟨headLe1, tailLe1⟩, ⟨headLe2, tailLe2⟩ =>
      ⟨GradeVector.le_trans firstHead secondHead thirdHead headLe1 headLe2,
       le_trans firstTail secondTail thirdTail tailLe1 tailLe2⟩

end GradeAttribution

/-! ## Wood/Atkey 2022 corrected Lam rule

The structural Lam rule's premise is encoded as the following
equational shape: the body's attribution decomposes as

```
bodyAttr = (paramGrade, lamAttr .scaleBy closureGrade)
```

Reading this from right to left: the inherited bindings' grades
in the body are exactly `lamAttr * closureGrade` pointwise.
Inverting: `lamAttr = bodyTail / closureGrade` — the context
division of fx_design.md §6.2.

The new binding's grade in the body must equal the lambda's
declared parameter grade `paramGrade`. -/

/-- The Wood/Atkey 2022 Lam-compatibility predicate.

Given:
* `paramGrade` — the lambda's declared parameter grade (e.g.,
  `1` for `own x` linear, `ω` for `ref x` shared, `0` for ghost)
* `closureGrade` — the lambda's overall multiplicity (e.g., `1`
  if invoked once, `ω` if replicable)
* `bodyAttr` — the body's attribution (in scope `scope + 1`)
* `lamAttr` — the candidate lambda attribution (in scope `scope`)

The predicate holds iff the body's attribution is exactly the
lambda's attribution scaled by `closureGrade`, with the new
binding's grade equal to `paramGrade`.

Existence of such `lamAttr` is the Wood/Atkey 2022 context
division.  In the Atkey 2018 rejection example, no `lamAttr`
exists when the body uses a captured linear variable multiple
times — the body's tail attribution would need to equal
`(ω * 0, ω * 1, ...) = (0, ω, ...)`, but the actual usage
might be `(0, 1, ...)`, which has no `lamAttr` solution. -/
def IsLamCompatible {dims : List Dimension} {scope : Nat}
    (paramGrade : GradeVector dims)
    (closureGrade : GradeVector dims)
    (bodyAttr : GradeAttribution dims (scope + 1))
    (lamAttr : GradeAttribution dims scope) : Prop :=
  bodyAttr = (paramGrade, GradeAttribution.scaleBy closureGrade lamAttr)

/-- Corrected Wood/Atkey Lam premise after context division has been
computed.

`availableAttr` is the divided inherited context `Gamma / p`.
The lambda body may use the freshly-bound parameter exactly at
`paramGrade`, and may use inherited bindings only within the divided
availability.  This is the check that rejects a linear variable
captured by an omega-multiplicity closure: after division its
availability is zero, so any positive inherited usage fails. -/
def IsLamCompatibleWithAvailable {dims : List Dimension} {scope : Nat}
    (paramGrade : GradeVector dims)
    (availableAttr : GradeAttribution dims scope)
    (bodyAttr : GradeAttribution dims (scope + 1)) : Prop :=
  bodyAttr.1 = paramGrade ∧
  GradeAttribution.le bodyAttr.2 availableAttr

/-! ## Trivial Lam-compatibility cases

Two zero-knowledge cases that hold trivially: the all-zero body
under any closure grade, and the singleton-at-zero body for a
unit-graded variable. -/

/-- The all-zero body attribution is Lam-compatible with any
closure grade, paired with `paramGrade = 0`.  Models a lambda
that doesn't use the new binding and doesn't mention any
inherited binding. -/
theorem IsLamCompatible.allZero {dims : List Dimension} {scope : Nat}
    (closureGrade : GradeVector dims) :
    IsLamCompatible
      (paramGrade := GradeVector.zero)
      closureGrade
      (bodyAttr := (GradeAttribution.zero : GradeAttribution dims (scope + 1)))
      (lamAttr := GradeAttribution.zero) := by
  show ((GradeVector.zero, GradeAttribution.zero) : GradeAttribution dims (scope + 1))
        = ((GradeVector.zero,
            GradeAttribution.scaleBy closureGrade GradeAttribution.zero)
            : GradeAttribution dims (scope + 1))
  rw [GradeAttribution.scaleBy_zero_attr]

/-- The all-zero body is compatible with zero divided availability:
it uses the parameter at grade zero and uses no inherited binding. -/
theorem IsLamCompatibleWithAvailable.allZeroAtZero {dims : List Dimension} {scope : Nat} :
    IsLamCompatibleWithAvailable
      (paramGrade := GradeVector.zero)
      (availableAttr := (GradeAttribution.zero : GradeAttribution dims scope))
      (bodyAttr := (GradeAttribution.zero : GradeAttribution dims (scope + 1))) :=
  ⟨rfl, GradeAttribution.le_refl GradeAttribution.zero⟩

/-! ## Var rule

`Γ, x :_r A |- x : A` produces a singleton attribution: `1` at
position x's index, `0` everywhere else.  This is the canonical
"variable usage" pattern. -/

/-- A `Term.var` at position `varPos` has the singleton attribution.
This is the explicit content of the Var rule per §6.2: "grade 0
everywhere, r at x" — at unit grade `r = 1`, the attribution is
`singleton varPos`. -/
def IsVarCompatible {dims : List Dimension} {scope : Nat}
    (varPos : Fin scope)
    (varAttr : GradeAttribution dims scope) : Prop :=
  varAttr = GradeAttribution.singleton varPos

/-- The canonical Var attribution at position 0 in scope-1 is the
singleton at 0, which equals `unitHead` (head = 1, tail = 0). -/
theorem IsVarCompatible.atZero {dims : List Dimension} :
    IsVarCompatible (varPos := (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))
      (varAttr := (GradeAttribution.unitHead : GradeAttribution dims 1)) := by
  rfl

/-! ## App rule

`Γ |-_p1 f, Γ |-_p2 a → Γ |-_(p1 + r * p2) f a` where `r` is
the function's parameter grade.  Captured by the
`IsAppCompatible` predicate: the result attribution is the sum
of `f`'s attribution plus `r * a's attribution`. -/

/-- The App rule's compatibility predicate.

Given:
* `paramGrade` — the function `f`'s declared parameter grade
* `functionAttr` — `f`'s attribution
* `argumentAttr` — `a`'s attribution
* `resultAttr` — the candidate result attribution

The predicate holds iff `resultAttr = functionAttr + paramGrade *
argumentAttr` pointwise.  This implements §6.2's
"App: G |-_(p1 + r * p2)". -/
def IsAppCompatible {dims : List Dimension} {scope : Nat}
    (paramGrade : GradeVector dims)
    (functionAttr argumentAttr : GradeAttribution dims scope)
    (resultAttr : GradeAttribution dims scope) : Prop :=
  resultAttr =
    GradeAttribution.add functionAttr
      (GradeAttribution.scaleBy paramGrade argumentAttr)

/-- App with all-zero attributions and any paramGrade is
trivially compatible: `0 + p * 0 = 0`.  Models an application
of a closed pure function to a closed pure argument. -/
theorem IsAppCompatible.allZero {dims : List Dimension} {scope : Nat}
    (paramGrade : GradeVector dims) :
    IsAppCompatible
      paramGrade
      (functionAttr := (GradeAttribution.zero : GradeAttribution dims scope))
      (argumentAttr := GradeAttribution.zero)
      (resultAttr := GradeAttribution.zero) := by
  show (GradeAttribution.zero : GradeAttribution dims scope)
        = GradeAttribution.add GradeAttribution.zero
            (GradeAttribution.scaleBy paramGrade GradeAttribution.zero)
  rw [GradeAttribution.scaleBy_zero_attr,
      GradeAttribution.add_zero_left]

/-! ## Let rule

`Γ |-_p1 e, Γ, x :_r A |-_p2 body → Γ |-_(r * p1 + p2) (let x = e in body)`.

Same shape as App but with the body in extended scope: the body's
attribution at the new binding is `r` (the let-binding's grade),
and the let-bound expression `e`'s attribution is scaled by `r`
when added to the body's tail. -/

/-- The Let rule's compatibility predicate.

Given:
* `bindingGrade` — the let-binding's declared grade `r`
* `boundAttr` — `e`'s attribution (the let-bound expression)
* `bodyAttr` — `body`'s attribution in scope+1
* `resultAttr` — the candidate result attribution in scope

The predicate holds iff:
* `bodyAttr.1 = bindingGrade` — body uses the let-binding at the
  declared grade (head of the pair)
* `resultAttr = bindingGrade * boundAttr + bodyAttr.2` pointwise
  (tail combines with scaled boundAttr) -/
def IsLetCompatible {dims : List Dimension} {scope : Nat}
    (bindingGrade : GradeVector dims)
    (boundAttr : GradeAttribution dims scope)
    (bodyAttr : GradeAttribution dims (scope + 1))
    (resultAttr : GradeAttribution dims scope) : Prop :=
  bodyAttr.1 = bindingGrade ∧
  resultAttr =
    GradeAttribution.add
      (GradeAttribution.scaleBy bindingGrade boundAttr)
      bodyAttr.2

/-! ## If/Match rule (join-as-add)

`Γ |-_p0 cond, Γ |-_p1 then, Γ |-_p2 else → Γ |-_(p0 + p1 ∨ p2)
if cond then ... else ...`.

Per fx_design.md §6.2, the join is "worst case — linear used in
both branches becomes unrestricted → error".  In the
usage-semiring instance, addition IS the join: `1 + 1 = ω`, so
expressing the join as pointwise addition is correct.  For other
semirings (security, lifetime, etc.) the join coincides with
addition by construction of the dimension's semiring. -/

/-- The If/Match rule's compatibility predicate.

Given:
* `conditionAttr` — the condition/scrutinee's attribution
* `thenAttr` — the `then`-branch's attribution
* `elseAttr` — the `else`-branch's attribution
* `resultAttr` — the candidate result attribution

The predicate holds iff `resultAttr = conditionAttr +
(thenAttr `add` elseAttr)`.  Per §6.2, branches' usages JOIN;
in our semiring framework, `add` IS the join (worst-case). -/
def IsIfCompatible {dims : List Dimension} {scope : Nat}
    (conditionAttr thenAttr elseAttr : GradeAttribution dims scope)
    (resultAttr : GradeAttribution dims scope) : Prop :=
  resultAttr =
    GradeAttribution.add conditionAttr
      (GradeAttribution.add thenAttr elseAttr)

/-! ## Subsumption rule

`Γ |-_p1 e : A, p1 ≤ p2 → Γ |-_p2 e : A`.

The Subsumption rule lets a less-restrictive (lower-grade)
attribution be used where a more-restrictive (higher-grade)
attribution is required.  Captured by the pointwise preorder. -/

/-- The Subsumption rule's compatibility predicate.

Given a strict attribution `tightAttr` and a loose attribution
`looseAttr`, the predicate holds iff `tightAttr ≤ looseAttr`
pointwise.  Subsumption permits using `tightAttr` where
`looseAttr` is required. -/
def IsSubsumptionCompatible {dims : List Dimension} {scope : Nat}
    (tightAttr looseAttr : GradeAttribution dims scope) : Prop :=
  GradeAttribution.le tightAttr looseAttr

/-- Subsumption is reflexive: every attribution subsumes itself. -/
theorem IsSubsumptionCompatible.refl {dims : List Dimension} {scope : Nat}
    (someAttr : GradeAttribution dims scope) :
    IsSubsumptionCompatible someAttr someAttr :=
  GradeAttribution.le_refl someAttr

/-- Subsumption is transitive. -/
theorem IsSubsumptionCompatible.trans {dims : List Dimension} {scope : Nat}
    (firstAttr secondAttr thirdAttr : GradeAttribution dims scope)
    (firstSub : IsSubsumptionCompatible firstAttr secondAttr)
    (secondSub : IsSubsumptionCompatible secondAttr thirdAttr) :
    IsSubsumptionCompatible firstAttr thirdAttr :=
  GradeAttribution.le_trans firstAttr secondAttr thirdAttr firstSub secondSub

/-! ## Smoke tests -/

/-- The empty-scope all-zero attribution is just `()`. -/
example {dims : List Dimension} :
    (GradeAttribution.zero : GradeAttribution dims 0) = () := rfl

/-- A 1-scope all-zero attribution has zero head and unit tail. -/
example {dims : List Dimension} :
    (GradeAttribution.zero : GradeAttribution dims 1)
      = (GradeVector.zero, ()) := rfl

/-- A 1-scope singleton at position 0 has unit head and unit tail. -/
example {dims : List Dimension} :
    GradeAttribution.singleton (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)
      = ((GradeVector.one, ()) : GradeAttribution dims 1) := rfl

/-- The Lam-rule all-zero compatibility holds for any closure grade. -/
example {dims : List Dimension} (closureGrade : GradeVector dims) :
    IsLamCompatible
      (paramGrade := GradeVector.zero)
      closureGrade
      (bodyAttr := (GradeAttribution.zero : GradeAttribution dims 1))
      (lamAttr := GradeAttribution.zero) :=
  IsLamCompatible.allZero closureGrade

/-- The App-rule all-zero compatibility holds for any param grade. -/
example {dims : List Dimension} (paramGrade : GradeVector dims) :
    IsAppCompatible
      paramGrade
      (functionAttr := (GradeAttribution.zero : GradeAttribution dims 0))
      (argumentAttr := GradeAttribution.zero)
      (resultAttr := GradeAttribution.zero) :=
  IsAppCompatible.allZero paramGrade

end LeanFX2.Graded
