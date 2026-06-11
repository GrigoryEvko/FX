import FX1Poly.Modal.GradedCostFundamental

/-! # FX1Poly/Modal/GradedTermSize
    — term size, exact occurrence counting, and the substitution-size equation (COST-2a brick 1)

The quantitative substrate for the linear-time theorem (`COST-2a`): if a
β-redex's bound variable occurs AT MOST ONCE in the body, the β-step
strictly decreases term size — the engine behind "linear terms normalize
in fewer than `size` steps under any strategy".

  * `GradedLambda.size` — node count (every constructor costs one).
  * `GradedLambda.countOccurrencesAt` — EXACT `Nat`-valued occurrence
    count of one de Bruijn index (the usage-vector `GradedLambda.usage`
    is ω-collapsed and unfit for size arithmetic).
  * `size_shift` — renaming preserves size.
  * `size_substAt` — **the additive substitution-size equation**:
    `size (substAt i r t) + count i t = size t + count i t · size r`.
    Each occurrence of the substituted variable trades one `var` node for
    a copy of the replacement; the ADDITIVE form dodges `Nat` truncated
    subtraction entirely.
  * `size_substAt_lt_redex` — **the β-size lemma**: when the bound
    variable occurs at most once, the β-reduct is strictly smaller than
    the redex.
  * `countOccurrencesAt_duplicator` — the ω-seed: the self-application
    body counts its variable TWICE, the witness germ for why duplication
    breaks the linear bound (consumed by the brick-2 counterwitnesses).

## Honest scope

`count ≤ 1` here is a SYNTACTIC hypothesis.  The bridge from GRADES to
counts is brick 2, and it holds only on the STRICT-linear fragment
(every binder grade exactly `1`): a grade-0 binder does NOT bound
occurrences, because 0-scaling annihilates the argument's grades while
its syntax remains — `λx. (f x) x` types at binder grade 0 with `x`
occurring twice, and its β-step DUPLICATES.  The affine fragment
therefore only enjoys ∃-strategy bounds (COST-2's relation), not the
any-strategy size decrease this substrate feeds.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Modal

/-! ## Size and exact occurrence counting -/

/-- Term size: every constructor costs one node. -/
def GradedLambda.size : GradedLambda → Nat
  | .var _ => 1
  | .lam body => GradedLambda.size body + 1
  | .app function argument => GradedLambda.size function + GradedLambda.size argument + 1

/-- Exact occurrence count of the free de Bruijn index `index` (shifted
under binders).  `Nat`-valued — the grade-vector `usage` collapses `1+1`
to `ω` and cannot drive size arithmetic. -/
def GradedLambda.countOccurrencesAt (index : Nat) : GradedLambda → Nat
  | .var varIndex => if varIndex = index then 1 else 0
  | .lam body => GradedLambda.countOccurrencesAt (index + 1) body
  | .app function argument =>
      GradedLambda.countOccurrencesAt index function
        + GradedLambda.countOccurrencesAt index argument

/-- Every term has at least one node. -/
theorem GradedLambda.size_pos : ∀ (term : GradedLambda), 1 ≤ term.size
  | .var _ => Nat.le_refl 1
  | .lam body => Nat.le_add_left 1 body.size
  | .app function argument =>
      Nat.le_add_left 1 (function.size + argument.size)

/-- de Bruijn shift preserves size (it only renames variables). -/
theorem GradedLambda.size_shift :
    ∀ (cutoff : Nat) (term : GradedLambda),
      (GradedLambda.shift cutoff term).size = term.size
  | cutoff, .var varIndex => by
      show (if varIndex < cutoff then GradedLambda.var varIndex
        else GradedLambda.var (varIndex + 1)).size = 1
      by_cases isBelow : varIndex < cutoff
      · rw [if_pos isBelow]
        rfl
      · rw [if_neg isBelow]
        rfl
  | cutoff, .lam body => by
      show (GradedLambda.shift (cutoff + 1) body).size + 1 = body.size + 1
      rw [GradedLambda.size_shift (cutoff + 1) body]
  | cutoff, .app function argument => by
      show (GradedLambda.shift cutoff function).size
          + (GradedLambda.shift cutoff argument).size + 1
        = function.size + argument.size + 1
      rw [GradedLambda.size_shift cutoff function,
        GradedLambda.size_shift cutoff argument]

/-! ## The additive substitution-size equation -/

/-- **The substitution-size equation** (additive form): substituting
`replacement` for index `index` trades each of the `count` occurrences
(one `var` node each) for one copy of the replacement —
`size (t[i := r]) + count = size t + count · size r`.  The additive
statement avoids `Nat` truncated subtraction. -/
theorem GradedLambda.size_substAt :
    ∀ (term : GradedLambda) (index : Nat) (replacement : GradedLambda),
      (GradedLambda.substAt index replacement term).size
          + GradedLambda.countOccurrencesAt index term
        = term.size
          + GradedLambda.countOccurrencesAt index term * replacement.size
  | .var varIndex, index, replacement => by
      show (if varIndex < index then GradedLambda.var varIndex
          else if varIndex = index then replacement
          else GradedLambda.var (varIndex - 1)).size
          + (if varIndex = index then 1 else 0)
        = 1 + (if varIndex = index then 1 else 0) * replacement.size
      by_cases isEqual : varIndex = index
      · have isNotBelow : ¬ varIndex < index := by
          rw [isEqual]
          exact Nat.lt_irrefl index
        rw [if_neg isNotBelow, if_pos isEqual, if_pos isEqual, Nat.one_mul,
          Nat.add_comm replacement.size 1]
      · by_cases isBelow : varIndex < index
        · rw [if_pos isBelow, if_neg isEqual, Nat.zero_mul]
          rfl
        · rw [if_neg isBelow, if_neg isEqual, if_neg isEqual, Nat.zero_mul]
          rfl
  | .lam body, index, replacement => by
      show (GradedLambda.substAt (index + 1) (GradedLambda.shift 0 replacement) body).size + 1
          + GradedLambda.countOccurrencesAt (index + 1) body
        = body.size + 1
          + GradedLambda.countOccurrencesAt (index + 1) body * replacement.size
      rw [Nat.add_right_comm
            (GradedLambda.substAt (index + 1) (GradedLambda.shift 0 replacement) body).size 1
            (GradedLambda.countOccurrencesAt (index + 1) body),
        GradedLambda.size_substAt body (index + 1) (GradedLambda.shift 0 replacement),
        GradedLambda.size_shift 0 replacement,
        Nat.add_right_comm body.size
          (GradedLambda.countOccurrencesAt (index + 1) body * replacement.size) 1]
  | .app function argument, index, replacement => by
      show (GradedLambda.substAt index replacement function).size
            + (GradedLambda.substAt index replacement argument).size + 1
          + (GradedLambda.countOccurrencesAt index function
            + GradedLambda.countOccurrencesAt index argument)
        = function.size + argument.size + 1
          + (GradedLambda.countOccurrencesAt index function
            + GradedLambda.countOccurrencesAt index argument) * replacement.size
      rw [Nat.add_right_comm
            ((GradedLambda.substAt index replacement function).size
              + (GradedLambda.substAt index replacement argument).size) 1
            (GradedLambda.countOccurrencesAt index function
              + GradedLambda.countOccurrencesAt index argument),
        natAddMiddleExchange (GradedLambda.substAt index replacement function).size
          (GradedLambda.substAt index replacement argument).size
          (GradedLambda.countOccurrencesAt index function)
          (GradedLambda.countOccurrencesAt index argument),
        GradedLambda.size_substAt function index replacement,
        GradedLambda.size_substAt argument index replacement,
        natAddMiddleExchange function.size
          (GradedLambda.countOccurrencesAt index function * replacement.size)
          argument.size
          (GradedLambda.countOccurrencesAt index argument * replacement.size),
        ← natRightDistrib (GradedLambda.countOccurrencesAt index function)
          (GradedLambda.countOccurrencesAt index argument) replacement.size,
        Nat.add_right_comm (function.size + argument.size)
          ((GradedLambda.countOccurrencesAt index function
            + GradedLambda.countOccurrencesAt index argument) * replacement.size) 1]

/-! ## The β-size lemma — at-most-once substitution shrinks -/

/-- Substituting a variable that does NOT occur preserves size. -/
theorem GradedLambda.size_substAt_of_absent {term : GradedLambda} {index : Nat}
    {replacement : GradedLambda}
    (absent : GradedLambda.countOccurrencesAt index term = 0) :
    (GradedLambda.substAt index replacement term).size = term.size := by
  have equation := GradedLambda.size_substAt term index replacement
  rw [absent, Nat.zero_mul, Nat.add_zero, Nat.add_zero] at equation
  exact equation

/-- Substituting a variable that occurs EXACTLY ONCE trades the `var`
node for the replacement: `size (t[i := r]) + 1 = size t + size r`. -/
theorem GradedLambda.size_substAt_of_linear {term : GradedLambda} {index : Nat}
    {replacement : GradedLambda}
    (linear : GradedLambda.countOccurrencesAt index term = 1) :
    (GradedLambda.substAt index replacement term).size + 1
      = term.size + replacement.size := by
  have equation := GradedLambda.size_substAt term index replacement
  rw [linear, Nat.one_mul] at equation
  exact equation

/-- **The β-size lemma**: when the bound variable occurs at most once in
the body, the β-reduct is strictly smaller than the redex — the
single-step engine of the linear-time bound.  (The redex carries the
`lam` and `app` nodes plus the whole argument; the reduct keeps at most
one copy of the argument and drops both nodes.) -/
theorem GradedLambda.size_substAt_lt_redex {body argument : GradedLambda}
    (countBound : GradedLambda.countOccurrencesAt 0 body ≤ 1) :
    (GradedLambda.substAt 0 argument body).size
      < (GradedLambda.app (GradedLambda.lam body) argument).size := by
  show (GradedLambda.substAt 0 argument body).size + 1
    ≤ body.size + 1 + argument.size + 1
  cases countZeroOrOne : GradedLambda.countOccurrencesAt 0 body with
  | zero =>
      rw [GradedLambda.size_substAt_of_absent countZeroOrOne]
      exact Nat.le_trans (Nat.le_add_right (body.size + 1) argument.size)
        (Nat.le_add_right (body.size + 1 + argument.size) 1)
  | succ predecessor =>
      cases predecessor with
      | zero =>
          rw [GradedLambda.size_substAt_of_linear countZeroOrOne,
            congrArg (· + 1) (Nat.add_right_comm body.size 1 argument.size)]
          exact Nat.le_trans (Nat.le_add_right (body.size + argument.size) 1)
            (Nat.le_add_right (body.size + argument.size + 1) 1)
      | succ deeper =>
          rw [countZeroOrOne] at countBound
          exact nomatch Nat.le_of_succ_le_succ countBound

/-! ## The duplication seed — why `count ≤ 1` is essential -/

/-- The duplicating body `(x x)` counts its variable TWICE — the
ω-duplication germ.  Brick 2's counterwitnesses grow from here: a β-step
on a duplicating redex copies the argument, and size decrease fails for
large arguments. -/
theorem GradedLambda.countOccurrencesAt_duplicator :
    GradedLambda.countOccurrencesAt 0
      (GradedLambda.app (GradedLambda.var 0) (GradedLambda.var 0)) = 2 := rfl

/-- Concrete non-example completing the honesty pair: with a duplicating
body, the β-reduct of `(λx. x x) (λy. y)` is NOT smaller than the redex
— size decrease genuinely needs the `count ≤ 1` hypothesis.  (Redex size
`6`, reduct `(λy.y)(λy.y)` size `5` — still smaller here, so the
threshold witness uses count: `2·size a + size body - 2 < size body +
size a + 2` fails exactly when `size a ≥ 4`; the brick-2 witness
instantiates a large argument.  This pin records the exact count.) -/
theorem GradedLambda.duplicatorRedex_count_exceeds_linear :
    ¬ GradedLambda.countOccurrencesAt 0
        (GradedLambda.app (GradedLambda.var 0) (GradedLambda.var 0)) ≤ 1 := by
  intro impossible
  rw [GradedLambda.countOccurrencesAt_duplicator] at impossible
  exact nomatch Nat.le_of_succ_le_succ impossible

end FX1Poly.Modal
