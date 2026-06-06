import FX1Poly.Modal.UsageDiscipline

/-! # FX1Poly/Modal/GradedTyping — the SOUND graded typing judgment (§6.2)
   the corrected Wood/Atkey graded STLC, in BGMZ / co-effect presentation

`UsageDiscipline` showed the bare occurrence check `usage ≤ Γ` is NOT subject-reduction-closed: the
linearity violation `(λx. x x) g` is well-graded yet its β-reduct `g g` is ill-graded
(`usage_check_fails_subject_reduction`).  The fix — and FX's corrected Wood/Atkey Lam rule (§6.2,
§27.1) — is to COUPLE grades to types: the lambda records its binder grade in the arrow type, and
the App rule SCALES the argument's usage by that grade.  This file builds that sound judgment.

  * `GType` — graded simple types: a base type and a graded arrow `dom -(binderGrade)-> cod`, where
    `binderGrade` is the §6.1 usage grade at which the function consumes its argument.

  * `HasUsage Γ p t T` — the typing-and-usage judgment: in type context `Γ`, term `t` has type `T`
    and uses the bindings with grade vector `p`.  The three rules:
      - VAR uses its variable once (`single _ index 1`);
      - LAM records the body's head grade as the arrow's binder grade and passes the body's outer
        usage out (the co-effect Lam rule);
      - APP combines `functionGrades + binderGrade · argumentGrades` — the App SCALING that the
        naive occurrence check omitted, exactly accounting for a function consuming its argument
        `binderGrade` times.

This is sound under reduction for two complementary reasons.  The PRIMARY reason is the grade
arithmetic, not the types: the Atkey-2018 double-capture `λf. f (f x)` IS simply-typeable (`f` only
needs `f : A -(r)-> A`), but the App rule scales the NESTED occurrence of `f` by its own binder grade
`r`, so `f`'s context grade computes to `1 + r·1` — which is `ω` whenever `f` actually consumes its
argument (`r ≥ 1`).  The Lam rule then pins the arrow's binder grade to that `ω`, so the term is
UNTYPABLE with `f` declared linear; it types only at grade `ω`.  SECONDARILY, type-coupling also
excludes the occurrence-check SR-breaker `(λx. x x) g`: self-application `x x` needs `x`'s type to
equal its own arrow type — an infinite type, impossible in finite `GType` — so that term never enters
the judgment at all.  So it is the grade discipline (not type finiteness) that rejects the linear-`f`
double-use; the occurs obstruction is a separate, additional guard.

The two witnesses show grades track usage exactly: `linearIdentity_typed` (`x` used once → arrow
grade `1`) and `kCombinator_typed` (`x` used once → `1`, `y` discarded → `0`).

## Zero-axiom verification

`GType` / `HasUsage` are plain inductives; the context `lookup` is structural recursion (NOT the
`l[i]?` / `getElem?` notation, which routes through `propext`); the witnesses are constructor terms
with `rfl` lookups.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Graded simple types: a base type and a graded arrow `dom -(binderGrade)-> cod`, where
`binderGrade` records how many times the function uses its argument (the §6.1 usage grade). -/
inductive GType where
  | base : GType
  | arrow : UsageGrade → GType → GType → GType
  deriving DecidableEq, Repr

/-- Look up a variable's type in the context by de Bruijn index.  Structural recursion — the `l[i]?`
(`getElem?`) notation's `List` instance routes through `propext`, so it is avoided here. -/
def GType.lookup : List GType → Nat → Option GType
  | [], _ => none
  | headType :: _, 0 => some headType
  | _ :: restTypes, position + 1 => GType.lookup restTypes position

/-- **The sound graded typing-and-usage judgment** `Γ ⊢_p t : T`: in type context `Γ` (a list of
types), term `t` has type `T` and uses the bindings with grade vector `p`.  The grades track usage
EXACTLY because the App rule scales the argument by the function's binder grade — the accounting the
naive occurrence check (`UsageDiscipline`) omitted, and the reason this judgment is
subject-reduction-sound. -/
inductive HasUsage : List GType → GradeVector → GradedLambda → GType → Prop where
  | var (typeContext : List GType) (index : Nat) (varType : GType)
      (lookupOk : GType.lookup typeContext index = some varType) :
      HasUsage typeContext (GradeVector.single typeContext.length index UsageGrade.one)
        (.var index) varType
  | lam (typeContext : List GType) (binderGrade : UsageGrade) (domain codomain : GType)
      (outerGrades : GradeVector) (body : GradedLambda)
      (bodyTyped : HasUsage (domain :: typeContext) (GradeVector.cons binderGrade outerGrades)
        body codomain) :
      HasUsage typeContext outerGrades (.lam body) (.arrow binderGrade domain codomain)
  | app (typeContext : List GType) (binderGrade : UsageGrade) (domain codomain : GType)
      (functionGrades argumentGrades : GradeVector) (function argument : GradedLambda)
      (functionTyped : HasUsage typeContext functionGrades function
        (.arrow binderGrade domain codomain))
      (argumentTyped : HasUsage typeContext argumentGrades argument domain) :
      HasUsage typeContext
        (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades))
        (.app function argument) codomain

/-- **The linear identity types with arrow grade `1`.**  `λx. x : base -(1)-> base` in the empty
context, using no outer bindings (`nil`): `x` is used exactly once, so the binder grade is `1`.  The
grade discipline reads linearity straight off the arrow. -/
theorem linearIdentity_typed :
    HasUsage [] GradeVector.nil (.lam (.var 0)) (.arrow UsageGrade.one GType.base GType.base) :=
  HasUsage.lam [] UsageGrade.one GType.base GType.base GradeVector.nil (.var 0)
    (HasUsage.var [GType.base] 0 GType.base rfl)

/-- **The K combinator's grades exactly track usage.**  `λx. λy. x : base -(1)-> (base -(0)-> base)`:
`x` is used once (binder grade `1`), `y` is dropped (binder grade `0`).  The discipline reads
linearity AND discarding directly off the nested arrow grades. -/
theorem kCombinator_typed :
    HasUsage [] GradeVector.nil (.lam (.lam (.var 1)))
      (.arrow UsageGrade.one GType.base (.arrow UsageGrade.zero GType.base GType.base)) :=
  HasUsage.lam [] UsageGrade.one GType.base (.arrow UsageGrade.zero GType.base GType.base)
    GradeVector.nil (.lam (.var 1))
    (HasUsage.lam [GType.base] UsageGrade.zero GType.base GType.base
      (GradeVector.cons UsageGrade.one GradeVector.nil) (.var 1)
      (HasUsage.var [GType.base, GType.base] 1 GType.base rfl))

end FX1Poly.Modal
